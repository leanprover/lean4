// Lean compiler output
// Module: Lean.Linter.List
// Imports: public import Lean.Linter.Basic public import Lean.Server.InfoUtils import Lean.Linter.Init
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "indexVariables"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(140, 104, 174, 176, 68, 7, 230, 32)}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "Validate that variables appearing as an index (e.g. in `xs[i]` or `xs.take i`) are only `i`, `j`, or `k`."};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 37, 25, 55, 115, 214, 21, 187)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(15, 84, 189, 165, 50, 238, 102, 128)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(157, 17, 204, 51, 209, 5, 242, 167)}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_linter_indexVariables;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "listVariables"};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(210, 104, 103, 104, 246, 30, 91, 67)}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Validate that all `List`/`Array`/`Vector` variables use allowed names."};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 37, 25, 55, 115, 214, 21, 187)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(15, 84, 189, 165, 50, 238, 102, 128)}};
static const lean_ctor_object l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 141, 236, 21, 178, 9, 197, 167)}};
static const lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_linter_listVariables;
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__0 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__1 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "zipIdx"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__2 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(136, 194, 118, 33, 195, 222, 129, 117)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__3 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eraseIdx!"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__4 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(222, 140, 125, 199, 125, 185, 235, 149)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__5 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "shrink"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__6 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(18, 53, 16, 214, 100, 18, 191, 53)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__7 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "drop"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__8 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(222, 63, 213, 104, 51, 86, 254, 30)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__9 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "take"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__10 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(65, 23, 32, 164, 148, 92, 18, 72)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__11 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 166, 17, 216, 125, 179, 132, 222)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__12 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eraseIdx"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__13 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 201, 72, 71, 56, 255, 95, 19)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__14 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(106, 246, 106, 249, 224, 85, 68, 146)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__15 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(205, 25, 66, 234, 231, 175, 30, 225)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__16 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__17 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 73, 216, 63, 47, 97, 234, 251)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__18 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(94, 254, 191, 187, 182, 154, 189, 137)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__19 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(146, 195, 13, 75, 237, 215, 49, 91)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__20 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(94, 145, 198, 121, 56, 216, 207, 226)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__21 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(193, 48, 133, 103, 235, 147, 189, 166)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__22 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "modify"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__23 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(190, 5, 193, 94, 64, 205, 30, 70)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__24 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eraseIdxIfInBounds"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__25 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value),LEAN_SCALAR_PTR_LITERAL(136, 5, 10, 10, 176, 131, 36, 61)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__26 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(114, 229, 173, 144, 205, 255, 115, 251)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__27 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "insertIdx!"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__28 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(67, 172, 64, 217, 46, 187, 199, 144)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__29 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "insertIdxIfInBounds"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__30 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value),LEAN_SCALAR_PTR_LITERAL(94, 238, 180, 209, 138, 243, 59, 10)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__31 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "setIfInBounds"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__32 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value),LEAN_SCALAR_PTR_LITERAL(76, 176, 191, 100, 168, 104, 38, 199)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__33 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__34 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value),LEAN_SCALAR_PTR_LITERAL(31, 2, 177, 81, 29, 192, 186, 111)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__35 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(138, 2, 71, 43, 166, 133, 203, 68)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__36 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "insertIdx"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__37 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value),LEAN_SCALAR_PTR_LITERAL(123, 109, 244, 207, 23, 221, 99, 50)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__38 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "set"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__39 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value),LEAN_SCALAR_PTR_LITERAL(149, 125, 231, 31, 126, 57, 111, 88)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__40 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(195, 186, 242, 84, 73, 231, 33, 9)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__41 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(242, 235, 217, 48, 226, 81, 229, 53)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__42 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value),LEAN_SCALAR_PTR_LITERAL(204, 22, 185, 115, 150, 146, 40, 66)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__43 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value),LEAN_SCALAR_PTR_LITERAL(159, 211, 128, 175, 184, 40, 61, 64)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__44 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "swap"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__45 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 162, 254, 94, 72, 66, 28)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__46 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value),LEAN_SCALAR_PTR_LITERAL(71, 53, 94, 141, 60, 249, 54, 14)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__47 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uset"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__48 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value),LEAN_SCALAR_PTR_LITERAL(94, 60, 218, 202, 150, 167, 67, 245)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__49 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value),LEAN_SCALAR_PTR_LITERAL(9, 27, 248, 22, 165, 105, 163, 43)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__50 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value),LEAN_SCALAR_PTR_LITERAL(193, 189, 102, 247, 123, 80, 42, 233)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__51 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value),LEAN_SCALAR_PTR_LITERAL(199, 187, 43, 91, 128, 145, 22, 210)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__52 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value),LEAN_SCALAR_PTR_LITERAL(137, 108, 233, 253, 150, 184, 88, 232)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__53 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "GetElem\?"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__54 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem\?"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__55 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 183, 124, 210, 168, 65, 205)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__56 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__57 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value;
static const lean_string_object l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__58 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value;
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l_Lean_Linter_List_numericalIndices___lam__2___closed__59 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_List_numericalIndices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_numericalIndices___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_numericalIndices___closed__0 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___closed__0_value;
static const lean_closure_object l_Lean_Linter_List_numericalIndices___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_numericalIndices___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_numericalIndices___closed__1 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___closed__1_value;
static const lean_closure_object l_Lean_Linter_List_numericalIndices___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_numericalIndices___lam__2___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalIndices___closed__0_value),((lean_object*)&l_Lean_Linter_List_numericalIndices___closed__1_value)} };
static const lean_object* l_Lean_Linter_List_numericalIndices___closed__2 = (const lean_object*)&l_Lean_Linter_List_numericalIndices___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__0(lean_object*);
static const lean_string_object l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 77, 183, 229, 104, 240, 130, 241)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__1 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 123, 231, 181, 109, 241, 236, 140)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__2 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 67, 17, 14, 131, 131, 189, 98)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__3 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__4 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value;
static const lean_string_object l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "range'"};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__5 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(112, 223, 146, 83, 118, 136, 28, 110)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__6 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(240, 208, 10, 228, 248, 70, 168, 150)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__7 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(36, 105, 217, 127, 193, 8, 191, 52)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__8 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value;
static const lean_string_object l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__9 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(235, 65, 196, 76, 247, 95, 193, 213)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__10 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(107, 168, 147, 224, 100, 148, 41, 41)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__11 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0),((lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(247, 254, 27, 73, 83, 86, 207, 8)}};
static const lean_object* l_Lean_Linter_List_numericalWidths___lam__1___closed__12 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_List_numericalWidths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_numericalWidths___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_numericalWidths___closed__0 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___closed__0_value;
static const lean_closure_object l_Lean_Linter_List_numericalWidths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_numericalWidths___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_List_numericalWidths___closed__0_value)} };
static const lean_object* l_Lean_Linter_List_numericalWidths___closed__1 = (const lean_object*)&l_Lean_Linter_List_numericalWidths___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths(lean_object*);
static const lean_string_object l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Linter_List_bitVecWidths___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Linter_List_bitVecWidths___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_List_bitVecWidths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_bitVecWidths___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_bitVecWidths___closed__0 = (const lean_object*)&l_Lean_Linter_List_bitVecWidths___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₁"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₂"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₃"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₄"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_stripBinderName(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__0 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__0_value;
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__1 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__1_value;
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__2 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__2_value;
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__3 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__3_value;
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__4 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__4_value;
static const lean_string_object l_Lean_Linter_List_allowedIndices___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__5 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__5_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__6 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__6_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__4_value),((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__6_value)}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__7 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__7_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__3_value),((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__7_value)}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__8 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__8_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__2_value),((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__8_value)}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__9 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__9_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__1_value),((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__9_value)}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__10 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__10_value;
static const lean_ctor_object l_Lean_Linter_List_allowedIndices___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__0_value),((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__10_value)}};
static const lean_object* l_Lean_Linter_List_allowedIndices___closed__11 = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedIndices = (const lean_object*)&l_Lean_Linter_List_allowedIndices___closed__11_value;
static const lean_string_object l_Lean_Linter_List_allowedWidths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__0 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__0_value;
static const lean_string_object l_Lean_Linter_List_allowedWidths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__1 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__1_value;
static const lean_string_object l_Lean_Linter_List_allowedWidths___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "l"};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__2 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__2_value;
static const lean_string_object l_Lean_Linter_List_allowedWidths___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__3 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__3_value;
static const lean_ctor_object l_Lean_Linter_List_allowedWidths___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__4 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__4_value;
static const lean_ctor_object l_Lean_Linter_List_allowedWidths___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__2_value),((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__4_value)}};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__5 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__5_value;
static const lean_ctor_object l_Lean_Linter_List_allowedWidths___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedIndices___closed__2_value),((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__5_value)}};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__6 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__6_value;
static const lean_ctor_object l_Lean_Linter_List_allowedWidths___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__1_value),((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__6_value)}};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__7 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__7_value;
static const lean_ctor_object l_Lean_Linter_List_allowedWidths___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__0_value),((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__7_value)}};
static const lean_object* l_Lean_Linter_List_allowedWidths___closed__8 = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedWidths = (const lean_object*)&l_Lean_Linter_List_allowedWidths___closed__8_value;
static const lean_string_object l_Lean_Linter_List_allowedBitVecWidths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Lean_Linter_List_allowedBitVecWidths___closed__0 = (const lean_object*)&l_Lean_Linter_List_allowedBitVecWidths___closed__0_value;
static const lean_ctor_object l_Lean_Linter_List_allowedBitVecWidths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedBitVecWidths___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_List_allowedBitVecWidths___closed__1 = (const lean_object*)&l_Lean_Linter_List_allowedBitVecWidths___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedBitVecWidths = (const lean_object*)&l_Lean_Linter_List_allowedBitVecWidths___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Forbidden variable appearing as a width: use `n` or `m`: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Forbidden variable appearing as a BitVec width: use `w`: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Forbidden variable appearing as an index: use `i`, `j`, or `k`: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_List_indexLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_indexLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_indexLinter___closed__0 = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_List_indexLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_indexLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_List_indexLinter___closed__1 = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_List_indexLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "indexLinter"};
static const lean_object* l_Lean_Linter_List_indexLinter___closed__2 = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_List_indexLinter___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_List_indexLinter___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_indexLinter___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_List_indexLinter___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_indexLinter___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 37, 25, 55, 115, 214, 21, 187)}};
static const lean_ctor_object l_Lean_Linter_List_indexLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_indexLinter___closed__3_value_aux_2),((lean_object*)&l_Lean_Linter_List_indexLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 166, 39, 65, 52, 244, 216, 94)}};
static const lean_object* l_Lean_Linter_List_indexLinter___closed__3 = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_List_indexLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_List_indexLinter___closed__1_value),((lean_object*)&l_Lean_Linter_List_indexLinter___closed__3_value)}};
static const lean_object* l_Lean_Linter_List_indexLinter___closed__4 = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_indexLinter = (const lean_object*)&l_Lean_Linter_List_indexLinter___closed__4_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__0 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__0_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__1 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__1_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__2 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__2_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "tl"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__3 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__3_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__4 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__4_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "xs"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__5 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__5_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ys"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__6 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__6_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "zs"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__7 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__7_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "as"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__8 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__8_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bs"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__9 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__9_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cs"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__10 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__10_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ds"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__11 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__11_value;
static const lean_string_object l_Lean_Linter_List_allowedListNames___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "acc"};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__12 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__12_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__13 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__13_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__11_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__13_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__14 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__14_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__10_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__14_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__15 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__15_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__9_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__15_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__16 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__16_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__8_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__16_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__17 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__17_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__7_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__17_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__18 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__18_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__6_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__18_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__19 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__19_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__5_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__19_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__20 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__20_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__4_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__20_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__21 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__21_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__3_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__21_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__22 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__22_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__2_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__22_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__23 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__23_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__1_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__23_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__24 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__24_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__0_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__24_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__25 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__25_value;
static const lean_ctor_object l_Lean_Linter_List_allowedListNames___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_allowedWidths___closed__2_value),((lean_object*)&l_Lean_Linter_List_allowedListNames___closed__25_value)}};
static const lean_object* l_Lean_Linter_List_allowedListNames___closed__26 = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__26_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedListNames = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__26_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedArrayNames = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__21_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_allowedVectorNames = (const lean_object*)&l_Lean_Linter_List_allowedListNames___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_List_binders___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Linter_List_binders___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_List_binders___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Linter_List_binders___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_binders___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Linter_List_binders___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_List_binders___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Linter_List_binders___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_List_binders___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Forbidden variable appearing as a `Array` name: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xss"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Forbidden variable appearing as a `List` name: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "L"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Forbidden variable appearing as a `Vector` name: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_List_listVariablesLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_List_listVariablesLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_List_listVariablesLinter___closed__0 = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_List_listVariablesLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_List_listVariablesLinter___closed__1 = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_List_listVariablesLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "listVariablesLinter"};
static const lean_object* l_Lean_Linter_List_listVariablesLinter___closed__2 = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 37, 25, 55, 115, 214, 21, 187)}};
static const lean_ctor_object l_Lean_Linter_List_listVariablesLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2),((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(178, 104, 155, 83, 102, 4, 128, 194)}};
static const lean_object* l_Lean_Linter_List_listVariablesLinter___closed__3 = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_List_listVariablesLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__1_value),((lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__3_value)}};
static const lean_object* l_Lean_Linter_List_listVariablesLinter___closed__4 = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_List_listVariablesLinter = (const lean_object*)&l_Lean_Linter_List_listVariablesLinter___closed__4_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_81_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__0(lean_object* v_i_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v_i_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__1(lean_object* v_i_87_, lean_object* v_j_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v_j_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_i_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(lean_object* v_i_92_, lean_object* v_stx_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
if (lean_obj_tag(v_a_94_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_stx_93_);
lean_dec_ref(v_i_92_);
v___x_96_ = lean_array_to_list(v_a_95_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; 
v_head_97_ = lean_ctor_get(v_a_94_, 0);
if (lean_obj_tag(v_head_97_) == 1)
{
lean_object* v_tail_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_113_; 
lean_inc_ref(v_head_97_);
v_tail_98_ = lean_ctor_get(v_a_94_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_a_94_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_a_94_, 0);
lean_dec(v_unused_114_);
v___x_100_ = v_a_94_;
v_isShared_101_ = v_isSharedCheck_113_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_tail_98_);
lean_dec(v_a_94_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_113_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_fvarId_102_; lean_object* v_lctx_103_; lean_object* v___x_104_; 
v_fvarId_102_ = lean_ctor_get(v_head_97_, 0);
lean_inc(v_fvarId_102_);
lean_dec_ref_known(v_head_97_, 1);
v_lctx_103_ = lean_ctor_get(v_i_92_, 1);
lean_inc_ref(v_lctx_103_);
v___x_104_ = lean_local_ctx_find(v_lctx_103_, v_fvarId_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_del_object(v___x_100_);
v_a_94_ = v_tail_98_;
goto _start;
}
else
{
lean_object* v_val_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v_val_106_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v___x_104_, 1);
v___x_107_ = l_Lean_LocalDecl_userName(v_val_106_);
lean_dec(v_val_106_);
lean_inc(v_stx_93_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
lean_ctor_set(v___x_100_, 1, v___x_107_);
lean_ctor_set(v___x_100_, 0, v_stx_93_);
v___x_109_ = v___x_100_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_stx_93_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_array_push(v_a_95_, v___x_109_);
v_a_94_ = v_tail_98_;
v_a_95_ = v___x_110_;
goto _start;
}
}
}
}
else
{
lean_object* v_tail_115_; 
v_tail_115_ = lean_ctor_get(v_a_94_, 1);
lean_inc(v_tail_115_);
lean_dec_ref_known(v_a_94_, 2);
v_a_94_ = v_tail_115_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2(lean_object* v___f_252_, lean_object* v___f_253_, lean_object* v_x_254_, lean_object* v_info_255_, lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_info_255_) == 1)
{
lean_object* v_i_257_; lean_object* v_expr_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_i_257_ = lean_ctor_get(v_info_255_, 0);
lean_inc_ref(v_i_257_);
v_expr_258_ = lean_ctor_get(v_i_257_, 3);
lean_inc_ref(v_expr_258_);
v___x_259_ = l_Lean_Expr_cleanupAnnotations(v_expr_258_);
v___x_260_ = l_Lean_Expr_isApp(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v___x_259_);
lean_dec_ref_known(v_info_255_, 1);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v_arg_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_arg_262_ = lean_ctor_get(v___x_259_, 1);
lean_inc_ref(v_arg_262_);
v___x_263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_259_);
v___x_264_ = l_Lean_Expr_isApp(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v_arg_262_);
lean_dec_ref_known(v_info_255_, 1);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_arg_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_arg_266_ = lean_ctor_get(v___x_263_, 1);
lean_inc_ref(v_arg_266_);
v___x_267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_263_);
v___x_268_ = l_Lean_Expr_isApp(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v___x_267_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref_known(v_info_255_, 1);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_269_ = lean_box(0);
return v___x_269_;
}
else
{
lean_object* v_arg_270_; lean_object* v_stx_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_411_; 
v_arg_270_ = lean_ctor_get(v___x_267_, 1);
lean_inc_ref(v_arg_270_);
v_stx_271_ = l_Lean_Elab_Info_stx(v_info_255_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_info_255_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_info_255_, 0);
lean_dec(v_unused_412_);
v___x_273_ = v_info_255_;
v_isShared_274_ = v_isSharedCheck_411_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_info_255_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_411_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___y_276_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_Expr_appFnCleanup___redArg(v___x_267_);
v___x_284_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__3));
v___x_285_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__5));
v___x_287_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__7));
v___x_289_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__9));
v___x_291_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__11));
v___x_293_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__12));
v___x_295_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__14));
v___x_297_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__15));
v___x_299_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__16));
v___x_301_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_300_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_Expr_isApp(v___x_283_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_303_ = lean_box(0);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_283_);
v___x_305_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__18));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__19));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__20));
v___x_310_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__21));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__22));
v___x_314_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__24));
v___x_316_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__26));
v___x_318_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__27));
v___x_320_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__29));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__31));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__33));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__35));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__36));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__38));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__40));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = l_Lean_Expr_isApp(v___x_304_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v___x_304_);
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_304_);
v___x_338_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__41));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__42));
v___x_341_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__43));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__44));
v___x_345_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__46));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__47));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__49));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__50));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_337_);
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
v___x_357_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__51));
v___x_358_ = l_Lean_Expr_isConstOf(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; 
lean_dec_ref(v___f_253_);
v___x_359_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__52));
v___x_360_ = l_Lean_Expr_isConstOf(v___x_356_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__53));
v___x_362_ = l_Lean_Expr_isConstOf(v___x_356_, v___x_361_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
lean_dec_ref(v_arg_270_);
v___x_363_ = l_Lean_Expr_isApp(v___x_356_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v___x_356_);
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_252_);
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_356_);
v___x_366_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__56));
v___x_367_ = l_Lean_Expr_isConstOf(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
lean_dec_ref(v_arg_262_);
v___x_368_ = l_Lean_Expr_isApp(v___x_365_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref(v___x_365_);
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_252_);
v___x_369_ = lean_box(0);
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_365_);
v___x_371_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__59));
v___x_372_ = l_Lean_Expr_isConstOf(v___x_370_, v___x_371_);
lean_dec_ref(v___x_370_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_i_257_);
lean_dec_ref(v___f_252_);
v___x_373_ = lean_box(0);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_374_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v___x_365_);
lean_dec_ref(v_arg_266_);
v___x_375_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_375_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
v___x_376_ = lean_apply_1(v___f_252_, v_arg_270_);
v___y_276_ = v___x_376_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
v___x_377_ = lean_apply_1(v___f_252_, v_arg_270_);
v___y_276_ = v___x_377_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_252_);
v___x_378_ = lean_apply_2(v___f_253_, v_arg_270_, v_arg_266_);
v___y_276_ = v___x_378_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_379_ = lean_apply_1(v___f_252_, v_arg_270_);
v___y_276_ = v___x_379_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_380_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_380_ = lean_apply_1(v___f_252_, v_arg_270_);
v___y_276_ = v___x_380_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_381_ = lean_apply_1(v___f_252_, v_arg_270_);
v___y_276_ = v___x_381_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_382_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_252_);
v___x_382_ = lean_apply_2(v___f_253_, v_arg_270_, v_arg_266_);
v___y_276_ = v___x_382_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v___f_252_);
v___x_383_ = lean_apply_2(v___f_253_, v_arg_266_, v_arg_262_);
v___y_276_ = v___x_383_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_384_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_384_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_385_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_385_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_386_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_386_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_387_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_387_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_387_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_388_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_388_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_389_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_389_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v___f_252_);
v___x_390_ = lean_apply_2(v___f_253_, v_arg_266_, v_arg_262_);
v___y_276_ = v___x_390_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_391_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_391_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_392_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_392_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_393_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_393_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_394_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_394_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_395_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_395_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_396_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_396_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_397_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_397_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_398_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_398_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_399_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_399_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_399_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_400_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_400_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_400_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_401_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_401_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_402_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_402_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_402_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_262_);
lean_dec_ref(v___f_253_);
v___x_403_ = lean_apply_1(v___f_252_, v_arg_266_);
v___y_276_ = v___x_403_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_404_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_404_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_405_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_405_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_406_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_406_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_407_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_407_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_408_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_408_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_408_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_409_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_409_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v___f_253_);
v___x_410_ = lean_apply_1(v___f_252_, v_arg_262_);
v___y_276_ = v___x_410_;
goto v___jp_275_;
}
v___jp_275_:
{
if (lean_obj_tag(v___y_276_) == 0)
{
lean_object* v___x_277_; 
lean_del_object(v___x_273_);
lean_dec(v_stx_271_);
lean_dec_ref(v_i_257_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_279_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_257_, v_stx_271_, v___y_276_, v___x_278_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_279_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v_info_255_);
lean_dec_ref(v___f_253_);
lean_dec_ref(v___f_252_);
v___x_413_ = lean_box(0);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2___boxed(lean_object* v___f_414_, lean_object* v___f_415_, lean_object* v_x_416_, lean_object* v_info_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Linter_List_numericalIndices___lam__2(v___f_414_, v___f_415_, v_x_416_, v_info_417_, v_x_418_);
lean_dec_ref(v_x_418_);
lean_dec_ref(v_x_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
if (lean_obj_tag(v_a_420_) == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_array_to_list(v_a_421_);
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v___x_425_; 
v_head_423_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_head_423_);
v_tail_424_ = lean_ctor_get(v_a_420_, 1);
lean_inc(v_tail_424_);
lean_dec_ref_known(v_a_420_, 2);
v___x_425_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_421_, v_head_423_);
v_a_420_ = v_tail_424_;
v_a_421_ = v___x_425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices(lean_object* v_t_432_){
_start:
{
lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___f_433_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___closed__2));
v___x_434_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_433_, v_t_432_);
v___x_435_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_436_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__0(lean_object* v_n_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_n_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1(lean_object* v___f_472_, lean_object* v_x_473_, lean_object* v_info_474_, lean_object* v_x_475_){
_start:
{
if (lean_obj_tag(v_info_474_) == 1)
{
lean_object* v_i_476_; lean_object* v_expr_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_i_476_ = lean_ctor_get(v_info_474_, 0);
lean_inc_ref(v_i_476_);
v_expr_477_ = lean_ctor_get(v_i_476_, 3);
lean_inc_ref(v_expr_477_);
v___x_478_ = l_Lean_Expr_cleanupAnnotations(v_expr_477_);
v___x_479_ = l_Lean_Expr_isApp(v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v___x_478_);
lean_dec_ref(v_i_476_);
lean_dec_ref_known(v_info_474_, 1);
lean_dec_ref(v___f_472_);
v___x_480_ = lean_box(0);
return v___x_480_;
}
else
{
lean_object* v_arg_481_; lean_object* v_stx_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_533_; 
v_arg_481_ = lean_ctor_get(v___x_478_, 1);
lean_inc_ref(v_arg_481_);
v_stx_482_ = l_Lean_Elab_Info_stx(v_info_474_);
v_isSharedCheck_533_ = !lean_is_exclusive(v_info_474_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_info_474_, 0);
lean_dec(v_unused_534_);
v___x_484_ = v_info_474_;
v_isShared_485_ = v_isSharedCheck_533_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_info_474_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_533_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___y_487_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = l_Lean_Expr_appFnCleanup___redArg(v___x_478_);
v___x_495_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__1));
v___x_496_ = l_Lean_Expr_isConstOf(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__2));
v___x_498_ = l_Lean_Expr_isConstOf(v___x_494_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__3));
v___x_500_ = l_Lean_Expr_isConstOf(v___x_494_, v___x_499_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_Expr_isApp(v___x_494_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v___x_494_);
lean_del_object(v___x_484_);
lean_dec(v_stx_482_);
lean_dec_ref(v_arg_481_);
lean_dec_ref(v_i_476_);
lean_dec_ref(v___f_472_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_arg_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_arg_503_ = lean_ctor_get(v___x_494_, 1);
lean_inc_ref(v_arg_503_);
v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_494_);
v___x_505_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_506_ = l_Lean_Expr_isConstOf(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
lean_dec_ref(v_arg_481_);
v___x_507_ = l_Lean_Expr_isApp(v___x_504_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v___x_504_);
lean_dec_ref(v_arg_503_);
lean_del_object(v___x_484_);
lean_dec(v_stx_482_);
lean_dec_ref(v_i_476_);
lean_dec_ref(v___f_472_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
v___x_510_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__6));
v___x_511_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__7));
v___x_513_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__8));
v___x_515_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__10));
v___x_517_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__11));
v___x_519_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__12));
v___x_521_ = l_Lean_Expr_isConstOf(v___x_509_, v___x_520_);
lean_dec_ref(v___x_509_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_arg_503_);
lean_del_object(v___x_484_);
lean_dec(v_stx_482_);
lean_dec_ref(v_i_476_);
lean_dec_ref(v___f_472_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_523_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_524_; 
lean_dec_ref(v___x_509_);
v___x_524_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_524_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec_ref(v___x_509_);
v___x_525_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_525_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v___x_509_);
v___x_526_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_526_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v___x_509_);
v___x_527_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_527_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_509_);
v___x_528_ = lean_apply_1(v___f_472_, v_arg_503_);
v___y_487_ = v___x_528_;
goto v___jp_486_;
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec_ref(v___x_504_);
lean_dec_ref(v_arg_503_);
v___x_529_ = lean_apply_1(v___f_472_, v_arg_481_);
v___y_487_ = v___x_529_;
goto v___jp_486_;
}
}
}
else
{
lean_object* v___x_530_; 
lean_dec_ref(v___x_494_);
v___x_530_ = lean_apply_1(v___f_472_, v_arg_481_);
v___y_487_ = v___x_530_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v___x_494_);
v___x_531_ = lean_apply_1(v___f_472_, v_arg_481_);
v___y_487_ = v___x_531_;
goto v___jp_486_;
}
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v___x_494_);
v___x_532_ = lean_apply_1(v___f_472_, v_arg_481_);
v___y_487_ = v___x_532_;
goto v___jp_486_;
}
v___jp_486_:
{
if (lean_obj_tag(v___y_487_) == 0)
{
lean_object* v___x_488_; 
lean_del_object(v___x_484_);
lean_dec(v_stx_482_);
lean_dec_ref(v_i_476_);
v___x_488_ = lean_box(0);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_489_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_490_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_476_, v_stx_482_, v___y_487_, v___x_489_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_490_);
v___x_492_ = v___x_484_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_info_474_);
lean_dec_ref(v___f_472_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1___boxed(lean_object* v___f_536_, lean_object* v_x_537_, lean_object* v_info_538_, lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Linter_List_numericalWidths___lam__1(v___f_536_, v_x_537_, v_info_538_, v_x_539_);
lean_dec_ref(v_x_539_);
lean_dec_ref(v_x_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths(lean_object* v_t_544_){
_start:
{
lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___f_545_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___closed__1));
v___x_546_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_545_, v_t_544_);
v___x_547_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_548_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0(lean_object* v_x_552_, lean_object* v_info_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_info_553_) == 1)
{
lean_object* v_i_555_; lean_object* v_expr_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_i_555_ = lean_ctor_get(v_info_553_, 0);
lean_inc_ref(v_i_555_);
v_expr_556_ = lean_ctor_get(v_i_555_, 3);
lean_inc_ref(v_expr_556_);
v___x_557_ = l_Lean_Expr_cleanupAnnotations(v_expr_556_);
v___x_558_ = l_Lean_Expr_isApp(v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec_ref(v___x_557_);
lean_dec_ref(v_i_555_);
lean_dec_ref_known(v_info_553_, 1);
v___x_559_ = lean_box(0);
return v___x_559_;
}
else
{
lean_object* v_arg_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_arg_560_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_arg_560_);
v___x_561_ = l_Lean_Expr_appFnCleanup___redArg(v___x_557_);
v___x_562_ = ((lean_object*)(l_Lean_Linter_List_bitVecWidths___lam__0___closed__1));
v___x_563_ = l_Lean_Expr_isConstOf(v___x_561_, v___x_562_);
lean_dec_ref(v___x_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec_ref(v_arg_560_);
lean_dec_ref(v_i_555_);
lean_dec_ref_known(v_info_553_, 1);
v___x_564_ = lean_box(0);
return v___x_564_;
}
else
{
lean_object* v_stx_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_576_; 
v_stx_565_ = l_Lean_Elab_Info_stx(v_info_553_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_info_553_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_info_553_, 0);
lean_dec(v_unused_577_);
v___x_567_ = v_info_553_;
v_isShared_568_ = v_isSharedCheck_576_;
goto v_resetjp_566_;
}
else
{
lean_dec(v_info_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_576_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v_arg_560_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_572_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_555_, v_stx_565_, v___x_570_, v___x_571_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_572_);
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v_info_553_);
v___x_578_ = lean_box(0);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0___boxed(lean_object* v_x_579_, lean_object* v_info_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Linter_List_bitVecWidths___lam__0(v_x_579_, v_info_580_, v_x_581_);
lean_dec_ref(v_x_581_);
lean_dec_ref(v_x_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths(lean_object* v_t_584_){
_start:
{
lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___f_585_ = ((lean_object*)(l_Lean_Linter_List_bitVecWidths___closed__0));
v___x_586_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_585_, v_t_584_);
v___x_587_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_588_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_586_, v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0));
v___x_591_ = lean_string_utf8_byte_size(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(lean_object* v_s_592_){
_start:
{
lean_object* v_str_593_; lean_object* v_startInclusive_594_; lean_object* v_endExclusive_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_str_593_ = lean_ctor_get(v_s_592_, 0);
v_startInclusive_594_ = lean_ctor_get(v_s_592_, 1);
v_endExclusive_595_ = lean_ctor_get(v_s_592_, 2);
v___x_596_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0));
v___x_597_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1, &l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1);
v___x_598_ = lean_nat_sub(v_endExclusive_595_, v_startInclusive_594_);
v___x_599_ = lean_nat_dec_le(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v___x_598_);
return v_s_592_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_sub(v___x_598_, v___x_597_);
lean_dec(v___x_598_);
v___x_602_ = lean_nat_add(v_startInclusive_594_, v___x_601_);
v___x_603_ = lean_string_memcmp(v_str_593_, v___x_596_, v___x_602_, v___x_600_, v___x_597_);
lean_dec(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v___x_601_);
return v_s_592_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
lean_inc(v_startInclusive_594_);
lean_inc_ref(v_str_593_);
v___x_604_ = l_String_Slice_pos_x21(v_s_592_, v___x_601_);
lean_dec(v___x_601_);
v_isSharedCheck_612_ = !lean_is_exclusive(v_s_592_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_613_ = lean_ctor_get(v_s_592_, 2);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_s_592_, 1);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_s_592_, 0);
lean_dec(v_unused_615_);
v___x_606_ = v_s_592_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_s_592_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_nat_add(v_startInclusive_594_, v___x_604_);
lean_dec(v___x_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_str_593_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_startInclusive_594_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0));
v___x_618_ = lean_string_utf8_byte_size(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(lean_object* v_s_619_){
_start:
{
lean_object* v_str_620_; lean_object* v_startInclusive_621_; lean_object* v_endExclusive_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_str_620_ = lean_ctor_get(v_s_619_, 0);
v_startInclusive_621_ = lean_ctor_get(v_s_619_, 1);
v_endExclusive_622_ = lean_ctor_get(v_s_619_, 2);
v___x_623_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0));
v___x_624_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1, &l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1);
v___x_625_ = lean_nat_sub(v_endExclusive_622_, v_startInclusive_621_);
v___x_626_ = lean_nat_dec_le(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v___x_625_);
return v_s_619_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_sub(v___x_625_, v___x_624_);
lean_dec(v___x_625_);
v___x_629_ = lean_nat_add(v_startInclusive_621_, v___x_628_);
v___x_630_ = lean_string_memcmp(v_str_620_, v___x_623_, v___x_629_, v___x_627_, v___x_624_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v___x_628_);
return v_s_619_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
lean_inc(v_startInclusive_621_);
lean_inc_ref(v_str_620_);
v___x_631_ = l_String_Slice_pos_x21(v_s_619_, v___x_628_);
lean_dec(v___x_628_);
v_isSharedCheck_639_ = !lean_is_exclusive(v_s_619_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_640_ = lean_ctor_get(v_s_619_, 2);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_s_619_, 1);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_s_619_, 0);
lean_dec(v_unused_642_);
v___x_633_ = v_s_619_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_s_619_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_nat_add(v_startInclusive_621_, v___x_631_);
lean_dec(v___x_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 2, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_str_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_startInclusive_621_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0));
v___x_645_ = lean_string_utf8_byte_size(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(lean_object* v_s_646_){
_start:
{
lean_object* v_str_647_; lean_object* v_startInclusive_648_; lean_object* v_endExclusive_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_str_647_ = lean_ctor_get(v_s_646_, 0);
v_startInclusive_648_ = lean_ctor_get(v_s_646_, 1);
v_endExclusive_649_ = lean_ctor_get(v_s_646_, 2);
v___x_650_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0));
v___x_651_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1, &l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1);
v___x_652_ = lean_nat_sub(v_endExclusive_649_, v_startInclusive_648_);
v___x_653_ = lean_nat_dec_le(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_dec(v___x_652_);
return v_s_646_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_sub(v___x_652_, v___x_651_);
lean_dec(v___x_652_);
v___x_656_ = lean_nat_add(v_startInclusive_648_, v___x_655_);
v___x_657_ = lean_string_memcmp(v_str_647_, v___x_650_, v___x_656_, v___x_654_, v___x_651_);
lean_dec(v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v___x_655_);
return v_s_646_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
lean_inc(v_startInclusive_648_);
lean_inc_ref(v_str_647_);
v___x_658_ = l_String_Slice_pos_x21(v_s_646_, v___x_655_);
lean_dec(v___x_655_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_s_646_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_667_ = lean_ctor_get(v_s_646_, 2);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_s_646_, 1);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_s_646_, 0);
lean_dec(v_unused_669_);
v___x_660_ = v_s_646_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_s_646_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_nat_add(v_startInclusive_648_, v___x_658_);
lean_dec(v___x_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_str_647_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_startInclusive_648_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0));
v___x_672_ = lean_string_utf8_byte_size(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(lean_object* v_s_673_){
_start:
{
lean_object* v_str_674_; lean_object* v_startInclusive_675_; lean_object* v_endExclusive_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_str_674_ = lean_ctor_get(v_s_673_, 0);
v_startInclusive_675_ = lean_ctor_get(v_s_673_, 1);
v_endExclusive_676_ = lean_ctor_get(v_s_673_, 2);
v___x_677_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0));
v___x_678_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1, &l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1);
v___x_679_ = lean_nat_sub(v_endExclusive_676_, v_startInclusive_675_);
v___x_680_ = lean_nat_dec_le(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec(v___x_679_);
return v_s_673_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_sub(v___x_679_, v___x_678_);
lean_dec(v___x_679_);
v___x_683_ = lean_nat_add(v_startInclusive_675_, v___x_682_);
v___x_684_ = lean_string_memcmp(v_str_674_, v___x_677_, v___x_683_, v___x_681_, v___x_678_);
lean_dec(v___x_683_);
if (v___x_684_ == 0)
{
lean_dec(v___x_682_);
return v_s_673_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
lean_inc(v_startInclusive_675_);
lean_inc_ref(v_str_674_);
v___x_685_ = l_String_Slice_pos_x21(v_s_673_, v___x_682_);
lean_dec(v___x_682_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_s_673_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_694_ = lean_ctor_get(v_s_673_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_s_673_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_s_673_, 0);
lean_dec(v_unused_696_);
v___x_687_ = v_s_673_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_s_673_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_nat_add(v_startInclusive_675_, v___x_685_);
lean_dec(v___x_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 2, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_startInclusive_675_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_699_ = lean_string_utf8_byte_size(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(lean_object* v_s_700_){
_start:
{
lean_object* v_str_701_; lean_object* v_startInclusive_702_; lean_object* v_endExclusive_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_str_701_ = lean_ctor_get(v_s_700_, 0);
v_startInclusive_702_ = lean_ctor_get(v_s_700_, 1);
v_endExclusive_703_ = lean_ctor_get(v_s_700_, 2);
v___x_704_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_705_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1);
v___x_706_ = lean_nat_sub(v_endExclusive_703_, v_startInclusive_702_);
v___x_707_ = lean_nat_dec_le(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v___x_706_);
return v_s_700_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_sub(v___x_706_, v___x_705_);
lean_dec(v___x_706_);
v___x_710_ = lean_nat_add(v_startInclusive_702_, v___x_709_);
v___x_711_ = lean_string_memcmp(v_str_701_, v___x_704_, v___x_710_, v___x_708_, v___x_705_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
lean_dec(v___x_709_);
return v_s_700_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
lean_inc(v_startInclusive_702_);
lean_inc_ref(v_str_701_);
v___x_712_ = l_String_Slice_pos_x21(v_s_700_, v___x_709_);
lean_dec(v___x_709_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_s_700_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; 
v_unused_721_ = lean_ctor_get(v_s_700_, 2);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_s_700_, 1);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_s_700_, 0);
lean_dec(v_unused_723_);
v___x_714_ = v_s_700_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_dec(v_s_700_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_nat_add(v_startInclusive_702_, v___x_712_);
lean_dec(v___x_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_str_701_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_startInclusive_702_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(lean_object* v_s_724_, lean_object* v_pat_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_string_utf8_byte_size(v_s_724_);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v_s_724_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(lean_object* v_s_730_, lean_object* v_pat_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_730_, v_pat_731_);
lean_dec_ref(v_pat_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_stripBinderName(lean_object* v_s_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_str_740_; lean_object* v_startInclusive_741_; lean_object* v_endExclusive_742_; lean_object* v___x_743_; 
v___x_734_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_735_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_733_, v___x_734_);
v___x_736_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(v___x_735_);
v___x_737_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(v___x_736_);
v___x_738_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(v___x_737_);
v___x_739_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(v___x_738_);
v_str_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_str_740_);
v_startInclusive_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_startInclusive_741_);
v_endExclusive_742_ = lean_ctor_get(v___x_739_, 2);
lean_inc(v_endExclusive_742_);
lean_dec_ref(v___x_739_);
v___x_743_ = lean_string_utf8_extract_fast(v_str_740_, v_startInclusive_741_, v_endExclusive_742_);
lean_dec(v_endExclusive_742_);
lean_dec(v_startInclusive_741_);
lean_dec_ref(v_str_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(lean_object* v_pat_744_, lean_object* v_s_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v_s_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(lean_object* v_pat_747_, lean_object* v_s_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(v_pat_747_, v_s_748_);
lean_dec_ref(v_pat_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_infoState_803_; lean_object* v_trees_804_; lean_object* v___x_805_; 
v___x_802_ = lean_st_ref_get(v___y_800_);
v_infoState_803_ = lean_ctor_get(v___x_802_, 8);
lean_inc_ref(v_infoState_803_);
lean_dec(v___x_802_);
v_trees_804_ = lean_ctor_get(v_infoState_803_, 2);
lean_inc_ref(v_trees_804_);
lean_dec_ref(v_infoState_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_trees_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_806_);
lean_dec(v___y_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(lean_object* v_opts_817_, lean_object* v_opt_818_){
_start:
{
lean_object* v_name_819_; lean_object* v_defValue_820_; lean_object* v_map_821_; lean_object* v___x_822_; 
v_name_819_ = lean_ctor_get(v_opt_818_, 0);
v_defValue_820_ = lean_ctor_get(v_opt_818_, 1);
v_map_821_ = lean_ctor_get(v_opts_817_, 0);
v___x_822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_821_, v_name_819_);
if (lean_obj_tag(v___x_822_) == 0)
{
uint8_t v___x_823_; 
v___x_823_ = lean_unbox(v_defValue_820_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; 
v_val_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_822_, 1);
if (lean_obj_tag(v_val_824_) == 1)
{
uint8_t v_v_825_; 
v_v_825_ = lean_ctor_get_uint8(v_val_824_, 0);
lean_dec_ref_known(v_val_824_, 0);
return v_v_825_;
}
else
{
uint8_t v___x_826_; 
lean_dec(v_val_824_);
v___x_826_ = lean_unbox(v_defValue_820_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_opts_827_, lean_object* v_opt_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_827_, v_opt_828_);
lean_dec_ref(v_opt_828_);
lean_dec_ref(v_opts_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_832_, uint8_t v___y_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 1)
{
lean_object* v_pre_835_; 
v_pre_835_ = lean_ctor_get(v_x_834_, 0);
if (lean_obj_tag(v_pre_835_) == 0)
{
lean_object* v_str_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_str_836_ = lean_ctor_get(v_x_834_, 1);
v___x_837_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_838_ = lean_string_dec_eq(v_str_836_, v___x_837_);
if (v___x_838_ == 0)
{
return v___x_838_;
}
else
{
return v_suppressElabErrors_832_;
}
}
else
{
return v___y_833_;
}
}
else
{
return v___y_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_839_, lean_object* v___y_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_suppressElabErrors_boxed_842_; uint8_t v___y_10893__boxed_843_; uint8_t v_res_844_; lean_object* v_r_845_; 
v_suppressElabErrors_boxed_842_ = lean_unbox(v_suppressElabErrors_839_);
v___y_10893__boxed_843_ = lean_unbox(v___y_840_);
v_res_844_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_842_, v___y_10893__boxed_843_, v_x_841_);
lean_dec(v_x_841_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_846_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_ctor_set(v___x_851_, 3, v___x_850_);
lean_ctor_set(v___x_851_, 4, v___x_849_);
lean_ctor_set(v___x_851_, 5, v___x_849_);
lean_ctor_set(v___x_851_, 6, v___x_849_);
lean_ctor_set(v___x_851_, 7, v___x_849_);
lean_ctor_set(v___x_851_, 8, v___x_849_);
lean_ctor_set(v___x_851_, 9, v___x_849_);
lean_ctor_set(v___x_851_, 10, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_unsigned_to_nat(32u);
v___x_853_ = lean_mk_empty_array_with_capacity(v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = ((size_t)5ULL);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_unsigned_to_nat(32u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3);
v___x_860_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
lean_ctor_set(v___x_860_, 2, v___x_856_);
lean_ctor_set(v___x_860_, 3, v___x_856_);
lean_ctor_set_usize(v___x_860_, 4, v___x_855_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(1);
v___x_862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4);
v___x_863_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_861_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(lean_object* v_msgData_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_env_869_; lean_object* v___x_870_; lean_object* v_scopes_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_opts_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_868_ = lean_st_ref_get(v___y_866_);
v_env_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc_ref(v_env_869_);
lean_dec(v___x_868_);
v___x_870_ = lean_st_ref_get(v___y_866_);
v_scopes_871_ = lean_ctor_get(v___x_870_, 2);
lean_inc(v_scopes_871_);
lean_dec(v___x_870_);
v___x_872_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_873_ = l_List_head_x21___redArg(v___x_872_, v_scopes_871_);
lean_dec(v_scopes_871_);
v_opts_874_ = lean_ctor_get(v___x_873_, 1);
lean_inc_ref(v_opts_874_);
lean_dec(v___x_873_);
v___x_875_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2);
v___x_876_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5);
v___x_877_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_877_, 0, v_env_869_);
lean_ctor_set(v___x_877_, 1, v___x_875_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set(v___x_877_, 3, v_opts_874_);
v___x_878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v_msgData_865_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_msgData_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_880_, v___y_881_);
lean_dec(v___y_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(lean_object* v_ref_885_, lean_object* v_msgData_886_, uint8_t v_severity_887_, uint8_t v_isSilent_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; uint8_t v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; uint8_t v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; uint8_t v___y_961_; lean_object* v___y_962_; uint8_t v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; uint8_t v___y_989_; lean_object* v___y_990_; uint8_t v___y_994_; uint8_t v___y_995_; uint8_t v___y_996_; uint8_t v___x_1011_; uint8_t v___y_1013_; uint8_t v___y_1014_; uint8_t v___y_1015_; uint8_t v___y_1017_; uint8_t v___x_1029_; 
v___x_1011_ = 2;
v___x_1029_ = l_Lean_instBEqMessageSeverity_beq(v_severity_887_, v___x_1011_);
if (v___x_1029_ == 0)
{
v___y_1017_ = v___x_1029_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1030_; 
lean_inc_ref(v_msgData_886_);
v___x_1030_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_886_);
v___y_1017_ = v___x_1030_;
goto v___jp_1016_;
}
v___jp_892_:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Elab_Command_getScope___redArg(v___y_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = l_Lean_Elab_Command_getScope___redArg(v___y_900_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_940_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_940_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_940_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_940_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v_currNamespace_909_; lean_object* v_openDecls_910_; lean_object* v_env_911_; lean_object* v_messages_912_; lean_object* v_scopes_913_; lean_object* v_usedQuotCtxts_914_; lean_object* v_nextMacroScope_915_; lean_object* v_maxRecDepth_916_; lean_object* v_ngen_917_; lean_object* v_auxDeclNGen_918_; lean_object* v_infoState_919_; lean_object* v_traceState_920_; lean_object* v_snapshotTasks_921_; lean_object* v_prevLinterStates_922_; lean_object* v_codeQualityEntryTasks_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_939_; 
v___x_908_ = lean_st_ref_take(v___y_900_);
v_currNamespace_909_ = lean_ctor_get(v_a_902_, 2);
lean_inc(v_currNamespace_909_);
lean_dec(v_a_902_);
v_openDecls_910_ = lean_ctor_get(v_a_904_, 3);
lean_inc(v_openDecls_910_);
lean_dec(v_a_904_);
v_env_911_ = lean_ctor_get(v___x_908_, 0);
v_messages_912_ = lean_ctor_get(v___x_908_, 1);
v_scopes_913_ = lean_ctor_get(v___x_908_, 2);
v_usedQuotCtxts_914_ = lean_ctor_get(v___x_908_, 3);
v_nextMacroScope_915_ = lean_ctor_get(v___x_908_, 4);
v_maxRecDepth_916_ = lean_ctor_get(v___x_908_, 5);
v_ngen_917_ = lean_ctor_get(v___x_908_, 6);
v_auxDeclNGen_918_ = lean_ctor_get(v___x_908_, 7);
v_infoState_919_ = lean_ctor_get(v___x_908_, 8);
v_traceState_920_ = lean_ctor_get(v___x_908_, 9);
v_snapshotTasks_921_ = lean_ctor_get(v___x_908_, 10);
v_prevLinterStates_922_ = lean_ctor_get(v___x_908_, 11);
v_codeQualityEntryTasks_923_ = lean_ctor_get(v___x_908_, 12);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_939_ == 0)
{
v___x_925_ = v___x_908_;
v_isShared_926_ = v_isSharedCheck_939_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_codeQualityEntryTasks_923_);
lean_inc(v_prevLinterStates_922_);
lean_inc(v_snapshotTasks_921_);
lean_inc(v_traceState_920_);
lean_inc(v_infoState_919_);
lean_inc(v_auxDeclNGen_918_);
lean_inc(v_ngen_917_);
lean_inc(v_maxRecDepth_916_);
lean_inc(v_nextMacroScope_915_);
lean_inc(v_usedQuotCtxts_914_);
lean_inc(v_scopes_913_);
lean_inc(v_messages_912_);
lean_inc(v_env_911_);
lean_dec(v___x_908_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_939_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_currNamespace_909_);
lean_ctor_set(v___x_927_, 1, v_openDecls_910_);
v___x_928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___y_897_);
lean_inc_ref(v___y_894_);
lean_inc_ref(v___y_893_);
v___x_929_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_929_, 0, v___y_893_);
lean_ctor_set(v___x_929_, 1, v___y_899_);
lean_ctor_set(v___x_929_, 2, v___y_898_);
lean_ctor_set(v___x_929_, 3, v___y_894_);
lean_ctor_set(v___x_929_, 4, v___x_928_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*5, v___y_896_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*5 + 1, v___y_895_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*5 + 2, v_isSilent_888_);
v___x_930_ = l_Lean_MessageLog_add(v___x_929_, v_messages_912_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_930_);
v___x_932_ = v___x_925_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_env_911_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_scopes_913_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_usedQuotCtxts_914_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_nextMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_938_, 5, v_maxRecDepth_916_);
lean_ctor_set(v_reuseFailAlloc_938_, 6, v_ngen_917_);
lean_ctor_set(v_reuseFailAlloc_938_, 7, v_auxDeclNGen_918_);
lean_ctor_set(v_reuseFailAlloc_938_, 8, v_infoState_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 9, v_traceState_920_);
lean_ctor_set(v_reuseFailAlloc_938_, 10, v_snapshotTasks_921_);
lean_ctor_set(v_reuseFailAlloc_938_, 11, v_prevLinterStates_922_);
lean_ctor_set(v_reuseFailAlloc_938_, 12, v_codeQualityEntryTasks_923_);
v___x_932_ = v_reuseFailAlloc_938_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_933_ = lean_st_ref_put(v___y_900_, v___x_932_);
v___x_934_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_934_);
v___x_936_ = v___x_906_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_902_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
v_a_941_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_903_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_903_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
v_a_949_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_901_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_901_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
v___jp_957_:
{
lean_object* v_fileName_963_; lean_object* v_fileMap_964_; uint8_t v_suppressElabErrors_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_984_; 
v_fileName_963_ = lean_ctor_get(v___y_889_, 0);
v_fileMap_964_ = lean_ctor_get(v___y_889_, 1);
v_suppressElabErrors_965_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*10);
v___x_966_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_886_);
v___x_967_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_966_, v___y_890_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_984_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_984_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_984_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref_n(v_fileMap_964_, 2);
v___x_972_ = l_Lean_FileMap_toPosition(v_fileMap_964_, v___y_959_);
lean_dec(v___y_959_);
v___x_973_ = l_Lean_FileMap_toPosition(v_fileMap_964_, v___y_962_);
lean_dec(v___y_962_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_965_ == 0)
{
lean_del_object(v___x_970_);
v___y_893_ = v_fileName_963_;
v___y_894_ = v___x_975_;
v___y_895_ = v___y_961_;
v___y_896_ = v___y_960_;
v___y_897_ = v_a_968_;
v___y_898_ = v___x_974_;
v___y_899_ = v___x_972_;
v___y_900_ = v___y_890_;
goto v___jp_892_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___f_978_; uint8_t v___x_979_; 
v___x_976_ = lean_box(v_suppressElabErrors_965_);
v___x_977_ = lean_box(v___y_958_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_978_, 0, v___x_976_);
lean_closure_set(v___f_978_, 1, v___x_977_);
lean_inc(v_a_968_);
v___x_979_ = l_Lean_MessageData_hasTag(v___f_978_, v_a_968_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_974_, 1);
lean_dec_ref(v___x_972_);
lean_dec(v_a_968_);
v___x_980_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_980_);
v___x_982_ = v___x_970_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_del_object(v___x_970_);
v___y_893_ = v_fileName_963_;
v___y_894_ = v___x_975_;
v___y_895_ = v___y_961_;
v___y_896_ = v___y_960_;
v___y_897_ = v_a_968_;
v___y_898_ = v___x_974_;
v___y_899_ = v___x_972_;
v___y_900_ = v___y_890_;
goto v___jp_892_;
}
}
}
}
v___jp_985_:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Syntax_getTailPos_x3f(v___y_987_, v___y_989_);
lean_dec(v___y_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_inc(v___y_990_);
v___y_958_ = v___y_986_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_989_;
v___y_961_ = v___y_988_;
v___y_962_ = v___y_990_;
goto v___jp_957_;
}
else
{
lean_object* v_val_992_; 
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
v___y_958_ = v___y_986_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_989_;
v___y_961_ = v___y_988_;
v___y_962_ = v_val_992_;
goto v___jp_957_;
}
}
v___jp_993_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Elab_Command_getRef___redArg(v___y_889_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v_ref_999_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v_ref_999_ = l_Lean_replaceRef(v_ref_885_, v_a_998_);
lean_dec(v_a_998_);
v___x_1000_ = l_Lean_Syntax_getPos_x3f(v_ref_999_, v___y_995_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___y_986_ = v___y_994_;
v___y_987_ = v_ref_999_;
v___y_988_ = v___y_996_;
v___y_989_ = v___y_995_;
v___y_990_ = v___x_1001_;
goto v___jp_985_;
}
else
{
lean_object* v_val_1002_; 
v_val_1002_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1000_, 1);
v___y_986_ = v___y_994_;
v___y_987_ = v_ref_999_;
v___y_988_ = v___y_996_;
v___y_989_ = v___y_995_;
v___y_990_ = v_val_1002_;
goto v___jp_985_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_msgData_886_);
v_a_1003_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_997_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_997_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
v___jp_1012_:
{
if (v___y_1015_ == 0)
{
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1014_;
v___y_996_ = v_severity_887_;
goto v___jp_993_;
}
else
{
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___x_1011_;
goto v___jp_993_;
}
}
v___jp_1016_:
{
if (v___y_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v_scopes_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_opts_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1018_ = lean_st_ref_get(v___y_890_);
v_scopes_1019_ = lean_ctor_get(v___x_1018_, 2);
lean_inc(v_scopes_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1021_ = l_List_head_x21___redArg(v___x_1020_, v_scopes_1019_);
lean_dec(v_scopes_1019_);
v_opts_1022_ = lean_ctor_get(v___x_1021_, 1);
lean_inc_ref(v_opts_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = 1;
v___x_1024_ = l_Lean_instBEqMessageSeverity_beq(v_severity_887_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v_opts_1022_);
v___y_1013_ = v___y_1017_;
v___y_1014_ = v___y_1017_;
v___y_1015_ = v___x_1024_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = l_Lean_warningAsError;
v___x_1026_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_1022_, v___x_1025_);
lean_dec_ref(v_opts_1022_);
v___y_1013_ = v___y_1017_;
v___y_1014_ = v___y_1017_;
v___y_1015_ = v___x_1026_;
goto v___jp_1012_;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_msgData_886_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1031_, lean_object* v_msgData_1032_, lean_object* v_severity_1033_, lean_object* v_isSilent_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v_severity_boxed_1038_; uint8_t v_isSilent_boxed_1039_; lean_object* v_res_1040_; 
v_severity_boxed_1038_ = lean_unbox(v_severity_1033_);
v_isSilent_boxed_1039_ = lean_unbox(v_isSilent_1034_);
v_res_1040_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1031_, v_msgData_1032_, v_severity_boxed_1038_, v_isSilent_boxed_1039_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v_ref_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(lean_object* v_ref_1041_, lean_object* v_msgData_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = 1;
v___x_1047_ = 0;
v___x_1048_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1041_, v_msgData_1042_, v___x_1046_, v___x_1047_, v___y_1043_, v___y_1044_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(lean_object* v_ref_1049_, lean_object* v_msgData_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_1049_, v_msgData_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v_ref_1049_);
return v_res_1054_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(lean_object* v_linterOption_1061_, lean_object* v_stx_1062_, lean_object* v_msg_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_name_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1085_; 
v_name_1067_ = lean_ctor_get(v_linterOption_1061_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_linterOption_1061_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_linterOption_1061_, 1);
lean_dec(v_unused_1086_);
v___x_1069_ = v_linterOption_1061_;
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_name_1067_);
lean_dec(v_linterOption_1061_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
lean_inc(v_name_1067_);
v___x_1072_ = l_Lean_MessageData_ofName(v_name_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 7);
lean_ctor_set(v___x_1069_, 1, v___x_1072_);
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_disable_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1075_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v_disable_1077_ = l_Lean_MessageData_note(v___x_1076_);
v___x_1078_ = l_Lean_Linter_linterMessageTag;
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_msg_1063_);
lean_ctor_set(v___x_1079_, 1, v_disable_1077_);
v___x_1080_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_name_1067_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
lean_inc(v_stx_1062_);
v___x_1082_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_stx_1062_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_1062_, v___x_1082_, v___y_1064_, v___y_1065_);
lean_dec(v_stx_1062_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(lean_object* v_linterOption_1087_, lean_object* v_stx_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v_linterOption_1087_, v_stx_1088_, v_msg_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(lean_object* v_a_1094_, lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
return v___x_1096_;
}
else
{
lean_object* v_head_1097_; lean_object* v_tail_1098_; uint8_t v___x_1099_; 
v_head_1097_ = lean_ctor_get(v_x_1095_, 0);
v_tail_1098_ = lean_ctor_get(v_x_1095_, 1);
v___x_1099_ = lean_string_dec_eq(v_a_1094_, v_head_1097_);
if (v___x_1099_ == 0)
{
v_x_1095_ = v_tail_1098_;
goto _start;
}
else
{
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(lean_object* v_a_1101_, lean_object* v_x_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_1101_, v_x_1102_);
lean_dec(v_x_1102_);
lean_dec_ref(v_a_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(lean_object* v_as_x27_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
if (lean_obj_tag(v_as_x27_1108_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1109_);
return v___x_1113_;
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1118_; 
v_head_1114_ = lean_ctor_get(v_as_x27_1108_, 0);
v_tail_1115_ = lean_ctor_get(v_as_x27_1108_, 1);
v_fst_1116_ = lean_ctor_get(v_head_1114_, 0);
v_snd_1117_ = lean_ctor_get(v_head_1114_, 1);
v___x_1118_ = lean_box(0);
if (lean_obj_tag(v_snd_1117_) == 1)
{
lean_object* v_str_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_str_1119_ = lean_ctor_get(v_snd_1117_, 1);
v___x_1120_ = ((lean_object*)(l_Lean_Linter_List_allowedWidths));
lean_inc_ref(v_str_1119_);
v___x_1121_ = l_Lean_Linter_List_stripBinderName(v_str_1119_);
v___x_1122_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1121_, v___x_1120_);
lean_dec_ref(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1123_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1124_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
lean_inc_ref(v_str_1119_);
v___x_1125_ = l_Lean_stringToMessageData(v_str_1119_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_inc(v_fst_1116_);
v___x_1127_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1123_, v_fst_1116_, v___x_1126_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_dec_ref_known(v___x_1127_, 1);
v_as_x27_1108_ = v_tail_1115_;
v_b_1109_ = v___x_1118_;
goto _start;
}
else
{
return v___x_1127_;
}
}
else
{
v_as_x27_1108_ = v_tail_1115_;
v_b_1109_ = v___x_1118_;
goto _start;
}
}
else
{
v_as_x27_1108_ = v_tail_1115_;
v_b_1109_ = v___x_1118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(lean_object* v_as_x27_1131_, lean_object* v_b_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1131_, v_b_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v_as_x27_1131_);
return v_res_1136_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(lean_object* v_as_x27_1140_, lean_object* v_b_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
if (lean_obj_tag(v_as_x27_1140_) == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_b_1141_);
return v___x_1145_;
}
else
{
lean_object* v_head_1146_; lean_object* v_tail_1147_; lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1150_; 
v_head_1146_ = lean_ctor_get(v_as_x27_1140_, 0);
v_tail_1147_ = lean_ctor_get(v_as_x27_1140_, 1);
v_fst_1148_ = lean_ctor_get(v_head_1146_, 0);
v_snd_1149_ = lean_ctor_get(v_head_1146_, 1);
v___x_1150_ = lean_box(0);
if (lean_obj_tag(v_snd_1149_) == 1)
{
lean_object* v_str_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_str_1151_ = lean_ctor_get(v_snd_1149_, 1);
v___x_1152_ = ((lean_object*)(l_Lean_Linter_List_allowedBitVecWidths));
lean_inc_ref(v_str_1151_);
v___x_1153_ = l_Lean_Linter_List_stripBinderName(v_str_1151_);
v___x_1154_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1153_, v___x_1152_);
lean_dec_ref(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1155_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1156_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
lean_inc_ref(v_str_1151_);
v___x_1157_ = l_Lean_stringToMessageData(v_str_1151_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
lean_inc(v_fst_1148_);
v___x_1159_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1155_, v_fst_1148_, v___x_1158_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_dec_ref_known(v___x_1159_, 1);
v_as_x27_1140_ = v_tail_1147_;
v_b_1141_ = v___x_1150_;
goto _start;
}
else
{
return v___x_1159_;
}
}
else
{
v_as_x27_1140_ = v_tail_1147_;
v_b_1141_ = v___x_1150_;
goto _start;
}
}
else
{
v_as_x27_1140_ = v_tail_1147_;
v_b_1141_ = v___x_1150_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(lean_object* v_as_x27_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1163_, v_b_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_as_x27_1163_);
return v_res_1168_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(lean_object* v_as_x27_1172_, lean_object* v_b_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
if (lean_obj_tag(v_as_x27_1172_) == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1173_);
return v___x_1177_;
}
else
{
lean_object* v_head_1178_; lean_object* v_tail_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; 
v_head_1178_ = lean_ctor_get(v_as_x27_1172_, 0);
v_tail_1179_ = lean_ctor_get(v_as_x27_1172_, 1);
v_fst_1180_ = lean_ctor_get(v_head_1178_, 0);
v_snd_1181_ = lean_ctor_get(v_head_1178_, 1);
v___x_1182_ = lean_box(0);
if (lean_obj_tag(v_snd_1181_) == 1)
{
lean_object* v_str_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_str_1183_ = lean_ctor_get(v_snd_1181_, 1);
v___x_1184_ = ((lean_object*)(l_Lean_Linter_List_allowedIndices));
lean_inc_ref(v_str_1183_);
v___x_1185_ = l_Lean_Linter_List_stripBinderName(v_str_1183_);
v___x_1186_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1185_, v___x_1184_);
lean_dec_ref(v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1187_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1188_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
lean_inc_ref(v_str_1183_);
v___x_1189_ = l_Lean_stringToMessageData(v_str_1183_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_inc(v_fst_1180_);
v___x_1191_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1187_, v_fst_1180_, v___x_1190_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref_known(v___x_1191_, 1);
v_as_x27_1172_ = v_tail_1179_;
v_b_1173_ = v___x_1182_;
goto _start;
}
else
{
return v___x_1191_;
}
}
else
{
v_as_x27_1172_ = v_tail_1179_;
v_b_1173_ = v___x_1182_;
goto _start;
}
}
else
{
v_as_x27_1172_ = v_tail_1179_;
v_b_1173_ = v___x_1182_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(lean_object* v_as_x27_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1195_, v_b_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v_as_x27_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(lean_object* v_as_1204_, size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_usize_dec_lt(v_i_1206_, v_sz_1205_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_b_1207_);
return v___x_1212_;
}
else
{
lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_b_1207_);
v___x_1213_ = lean_box(0);
v_a_1214_ = lean_array_uget_borrowed(v_as_1204_, v_i_1206_);
lean_inc(v_a_1214_);
v___x_1215_ = l_Lean_Linter_List_numericalIndices(v_a_1214_);
v___x_1216_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1215_, v___x_1213_, v___y_1208_, v___y_1209_);
lean_dec(v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref_known(v___x_1216_, 1);
lean_inc(v_a_1214_);
v___x_1217_ = l_Lean_Linter_List_numericalWidths(v_a_1214_);
v___x_1218_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1217_, v___x_1213_, v___y_1208_, v___y_1209_);
lean_dec(v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref_known(v___x_1218_, 1);
lean_inc(v_a_1214_);
v___x_1219_ = l_Lean_Linter_List_bitVecWidths(v_a_1214_);
v___x_1220_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1219_, v___x_1213_, v___y_1208_, v___y_1209_);
lean_dec(v___x_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1206_, v___x_1222_);
v_i_1206_ = v___x_1223_;
v_b_1207_ = v___x_1221_;
goto _start;
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1220_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1220_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1218_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1218_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1216_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1216_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(lean_object* v_as_1249_, lean_object* v_sz_1250_, lean_object* v_i_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
size_t v_sz_boxed_1256_; size_t v_i_boxed_1257_; lean_object* v_res_1258_; 
v_sz_boxed_1256_ = lean_unbox_usize(v_sz_1250_);
lean_dec(v_sz_1250_);
v_i_boxed_1257_ = lean_unbox_usize(v_i_1251_);
lean_dec(v_i_1251_);
v_res_1258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1249_, v_sz_boxed_1256_, v_i_boxed_1257_, v_b_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_as_1249_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(lean_object* v_as_1259_, size_t v_sz_1260_, size_t v_i_1261_, lean_object* v_b_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1261_, v_sz_1260_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1262_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_b_1262_);
v___x_1268_ = lean_box(0);
v_a_1269_ = lean_array_uget_borrowed(v_as_1259_, v_i_1261_);
lean_inc(v_a_1269_);
v___x_1270_ = l_Lean_Linter_List_numericalIndices(v_a_1269_);
v___x_1271_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1270_, v___x_1268_, v___y_1263_, v___y_1264_);
lean_dec(v___x_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref_known(v___x_1271_, 1);
lean_inc(v_a_1269_);
v___x_1272_ = l_Lean_Linter_List_numericalWidths(v_a_1269_);
v___x_1273_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1272_, v___x_1268_, v___y_1263_, v___y_1264_);
lean_dec(v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec_ref_known(v___x_1273_, 1);
lean_inc(v_a_1269_);
v___x_1274_ = l_Lean_Linter_List_bitVecWidths(v_a_1269_);
v___x_1275_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1274_, v___x_1268_, v___y_1263_, v___y_1264_);
lean_dec(v___x_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1275_, 1);
v___x_1276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_add(v_i_1261_, v___x_1277_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1259_, v_sz_1260_, v___x_1278_, v___x_1276_, v___y_1263_, v___y_1264_);
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1275_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1275_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1273_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1273_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1271_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1271_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_as_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_1304_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v_as_1304_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(lean_object* v_init_1314_, lean_object* v_n_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
if (lean_obj_tag(v_n_1315_) == 0)
{
lean_object* v_cs_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; size_t v_sz_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v_cs_1320_ = lean_ctor_get(v_n_1315_, 0);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_b_1316_);
v_sz_1323_ = lean_array_size(v_cs_1320_);
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1314_, v_cs_1320_, v_sz_1323_, v___x_1324_, v___x_1322_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1340_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_fst_1330_; 
v_fst_1330_ = lean_ctor_get(v_a_1326_, 0);
if (lean_obj_tag(v_fst_1330_) == 0)
{
lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v_snd_1331_ = lean_ctor_get(v_a_1326_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1326_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_snd_1331_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1332_);
v___x_1334_ = v___x_1328_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v_val_1336_; lean_object* v___x_1338_; 
lean_inc_ref(v_fst_1330_);
lean_dec(v_a_1326_);
v_val_1336_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_fst_1330_, 1);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_val_1336_);
v___x_1338_ = v___x_1328_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_val_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1325_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1325_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_vs_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v_vs_1349_ = lean_ctor_get(v_n_1315_, 0);
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v_b_1316_);
v_sz_1352_ = lean_array_size(v_vs_1349_);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_1349_, v_sz_1352_, v___x_1353_, v___x_1351_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1369_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1369_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1369_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_fst_1359_; 
v_fst_1359_ = lean_ctor_get(v_a_1355_, 0);
if (lean_obj_tag(v_fst_1359_) == 0)
{
lean_object* v_snd_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v_snd_1360_ = lean_ctor_get(v_a_1355_, 1);
lean_inc(v_snd_1360_);
lean_dec(v_a_1355_);
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_snd_1360_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1361_);
v___x_1363_ = v___x_1357_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1367_; 
lean_inc_ref(v_fst_1359_);
lean_dec(v_a_1355_);
v_val_1365_ = lean_ctor_get(v_fst_1359_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v_fst_1359_, 1);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_val_1365_);
v___x_1367_ = v___x_1357_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_val_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1354_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1354_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(lean_object* v_init_1378_, lean_object* v_as_1379_, size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_usize_dec_lt(v_i_1381_, v_sz_1380_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_b_1382_);
return v___x_1387_;
}
else
{
lean_object* v_snd_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1422_; 
v_snd_1388_ = lean_ctor_get(v_b_1382_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_b_1382_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_b_1382_, 0);
lean_dec(v_unused_1423_);
v___x_1390_ = v_b_1382_;
v_isShared_1391_ = v_isSharedCheck_1422_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_snd_1388_);
lean_dec(v_b_1382_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1422_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_array_uget_borrowed(v_as_1379_, v_i_1381_);
lean_inc(v_snd_1388_);
v___x_1393_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1378_, v_a_1392_, v_snd_1388_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1413_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1413_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1413_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
if (lean_obj_tag(v_a_1394_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_a_1394_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1398_);
v___x_1400_ = v___x_1390_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1388_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1400_);
v___x_1402_ = v___x_1396_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_del_object(v___x_1396_);
lean_dec(v_snd_1388_);
v_a_1405_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v_a_1394_, 1);
v___x_1406_ = lean_box(0);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v_a_1405_);
lean_ctor_set(v___x_1390_, 0, v___x_1406_);
v___x_1408_ = v___x_1390_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_a_1405_);
v___x_1408_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
size_t v___x_1409_; size_t v___x_1410_; 
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1381_, v___x_1409_);
v_i_1381_ = v___x_1410_;
v_b_1382_ = v___x_1408_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_del_object(v___x_1390_);
lean_dec(v_snd_1388_);
v_a_1414_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1393_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1393_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(lean_object* v_init_1424_, lean_object* v_as_1425_, lean_object* v_sz_1426_, lean_object* v_i_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
size_t v_sz_boxed_1432_; size_t v_i_boxed_1433_; lean_object* v_res_1434_; 
v_sz_boxed_1432_ = lean_unbox_usize(v_sz_1426_);
lean_dec(v_sz_1426_);
v_i_boxed_1433_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1424_, v_as_1425_, v_sz_boxed_1432_, v_i_boxed_1433_, v_b_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec_ref(v_as_1425_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(lean_object* v_init_1435_, lean_object* v_n_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1435_, v_n_1436_, v_b_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_n_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(lean_object* v_as_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_b_1448_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_b_1448_);
v___x_1454_ = lean_box(0);
v_a_1455_ = lean_array_uget_borrowed(v_as_1445_, v_i_1447_);
lean_inc(v_a_1455_);
v___x_1456_ = l_Lean_Linter_List_numericalIndices(v_a_1455_);
v___x_1457_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1456_, v___x_1454_, v___y_1449_, v___y_1450_);
lean_dec(v___x_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref_known(v___x_1457_, 1);
lean_inc(v_a_1455_);
v___x_1458_ = l_Lean_Linter_List_numericalWidths(v_a_1455_);
v___x_1459_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1458_, v___x_1454_, v___y_1449_, v___y_1450_);
lean_dec(v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref_known(v___x_1459_, 1);
lean_inc(v_a_1455_);
v___x_1460_ = l_Lean_Linter_List_bitVecWidths(v_a_1455_);
v___x_1461_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1460_, v___x_1454_, v___y_1449_, v___y_1450_);
lean_dec(v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; 
lean_dec_ref_known(v___x_1461_, 1);
v___x_1462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1447_, v___x_1463_);
v_i_1447_ = v___x_1464_;
v_b_1448_ = v___x_1462_;
goto _start;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1461_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1461_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1459_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1459_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1457_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1457_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(lean_object* v_as_1490_, lean_object* v_sz_1491_, lean_object* v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1491_);
lean_dec(v_sz_1491_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1490_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v_as_1490_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(lean_object* v_as_1500_, size_t v_sz_1501_, size_t v_i_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_lt(v_i_1502_, v_sz_1501_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_b_1503_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec_ref(v_b_1503_);
v___x_1509_ = lean_box(0);
v_a_1510_ = lean_array_uget_borrowed(v_as_1500_, v_i_1502_);
lean_inc(v_a_1510_);
v___x_1511_ = l_Lean_Linter_List_numericalIndices(v_a_1510_);
v___x_1512_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1511_, v___x_1509_, v___y_1504_, v___y_1505_);
lean_dec(v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v___x_1512_, 1);
lean_inc(v_a_1510_);
v___x_1513_ = l_Lean_Linter_List_numericalWidths(v_a_1510_);
v___x_1514_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1513_, v___x_1509_, v___y_1504_, v___y_1505_);
lean_dec(v___x_1513_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1514_, 1);
lean_inc(v_a_1510_);
v___x_1515_ = l_Lean_Linter_List_bitVecWidths(v_a_1510_);
v___x_1516_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1515_, v___x_1509_, v___y_1504_, v___y_1505_);
lean_dec(v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref_known(v___x_1516_, 1);
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1502_, v___x_1518_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1500_, v_sz_1501_, v___x_1519_, v___x_1517_, v___y_1504_, v___y_1505_);
return v___x_1520_;
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1516_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1516_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1514_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1514_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1512_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1512_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
size_t v_sz_boxed_1552_; size_t v_i_boxed_1553_; lean_object* v_res_1554_; 
v_sz_boxed_1552_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1553_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_1545_, v_sz_boxed_1552_, v_i_boxed_1553_, v_b_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_as_1545_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(lean_object* v_t_1555_, lean_object* v_init_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_root_1560_; lean_object* v_tail_1561_; lean_object* v___x_1562_; 
v_root_1560_ = lean_ctor_get(v_t_1555_, 0);
v_tail_1561_ = lean_ctor_get(v_t_1555_, 1);
v___x_1562_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1556_, v_root_1560_, v_init_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1599_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
if (lean_obj_tag(v_a_1563_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v_a_1563_, 1);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_a_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_del_object(v___x_1565_);
v_a_1571_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_a_1563_, 1);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_a_1571_);
v_sz_1574_ = lean_array_size(v_tail_1561_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_1561_, v_sz_1574_, v___x_1575_, v___x_1573_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_fst_1581_; 
v_fst_1581_ = lean_ctor_get(v_a_1577_, 0);
if (lean_obj_tag(v_fst_1581_) == 0)
{
lean_object* v_snd_1582_; lean_object* v___x_1584_; 
v_snd_1582_ = lean_ctor_get(v_a_1577_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_snd_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_snd_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1588_; 
lean_inc_ref(v_fst_1581_);
lean_dec(v_a_1577_);
v_val_1586_ = lean_ctor_get(v_fst_1581_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_fst_1581_, 1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_val_1586_);
v___x_1588_ = v___x_1579_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_val_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1576_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1576_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1562_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1562_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(lean_object* v_t_1608_, lean_object* v_init_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_t_1608_, v_init_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v_t_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0(lean_object* v_stx_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v_scopes_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_opts_1625_; lean_object* v___x_1626_; lean_object* v_name_1627_; lean_object* v_map_1628_; lean_object* v___x_1629_; 
v___x_1618_ = lean_st_ref_get(v___y_1616_);
v_scopes_1622_ = lean_ctor_get(v___x_1618_, 2);
lean_inc(v_scopes_1622_);
lean_dec(v___x_1618_);
v___x_1623_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1624_ = l_List_head_x21___redArg(v___x_1623_, v_scopes_1622_);
lean_dec(v_scopes_1622_);
v_opts_1625_ = lean_ctor_get(v___x_1624_, 1);
lean_inc_ref(v_opts_1625_);
lean_dec(v___x_1624_);
v___x_1626_ = l_Lean_Linter_List_linter_indexVariables;
v_name_1627_ = lean_ctor_get(v___x_1626_, 0);
v_map_1628_ = lean_ctor_get(v_opts_1625_, 0);
lean_inc(v_map_1628_);
lean_dec_ref(v_opts_1625_);
v___x_1629_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1628_, v_name_1627_);
lean_dec(v_map_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
goto v___jp_1619_;
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1662_; 
v_val_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1662_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1662_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
if (lean_obj_tag(v_val_1630_) == 1)
{
uint8_t v_v_1634_; 
v_v_1634_ = lean_ctor_get_uint8(v_val_1630_, 0);
lean_dec_ref_known(v_val_1630_, 0);
if (v_v_1634_ == 0)
{
lean_del_object(v___x_1632_);
goto v___jp_1619_;
}
else
{
lean_object* v___x_1635_; lean_object* v_messages_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_st_ref_get(v___y_1616_);
v_messages_1636_ = lean_ctor_get(v___x_1635_, 1);
lean_inc_ref(v_messages_1636_);
lean_dec(v___x_1635_);
v___x_1637_ = l_Lean_MessageLog_hasErrors(v_messages_1636_);
lean_dec_ref(v_messages_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v_infoState_1644_; uint8_t v_enabled_1645_; 
v___x_1638_ = lean_st_ref_get(v___y_1616_);
v_infoState_1644_ = lean_ctor_get(v___x_1638_, 8);
lean_inc_ref(v_infoState_1644_);
lean_dec(v___x_1638_);
v_enabled_1645_ = lean_ctor_get_uint8(v_infoState_1644_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1644_);
if (v_enabled_1645_ == 0)
{
goto v___jp_1639_;
}
else
{
if (v___x_1637_ == 0)
{
lean_object* v___x_1646_; lean_object* v_a_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_del_object(v___x_1632_);
v___x_1646_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_1616_);
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = lean_box(0);
v___x_1649_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_1647_, v___x_1648_, v___y_1615_, v___y_1616_);
lean_dec(v_a_1647_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1649_, 0);
lean_dec(v_unused_1657_);
v___x_1651_ = v___x_1649_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_dec(v___x_1649_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1648_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
return v___x_1649_;
}
}
else
{
goto v___jp_1639_;
}
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1640_);
v___x_1642_ = v___x_1632_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1658_);
v___x_1660_ = v___x_1632_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_del_object(v___x_1632_);
lean_dec(v_val_1630_);
goto v___jp_1619_;
}
}
}
v___jp_1619_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0___boxed(lean_object* v_stx_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v_stx_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(lean_object* v_as_1681_, lean_object* v_as_x27_1682_, lean_object* v_b_1683_, lean_object* v_a_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1682_, v_b_1683_, v___y_1685_, v___y_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(lean_object* v_as_1689_, lean_object* v_as_x27_1690_, lean_object* v_b_1691_, lean_object* v_a_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(v_as_1689_, v_as_x27_1690_, v_b_1691_, v_a_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v_as_x27_1690_);
lean_dec(v_as_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(lean_object* v_as_1697_, lean_object* v_as_x27_1698_, lean_object* v_b_1699_, lean_object* v_a_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1698_, v_b_1699_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(lean_object* v_as_1705_, lean_object* v_as_x27_1706_, lean_object* v_b_1707_, lean_object* v_a_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(v_as_1705_, v_as_x27_1706_, v_b_1707_, v_a_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_as_x27_1706_);
lean_dec(v_as_1705_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(lean_object* v_as_1713_, lean_object* v_as_x27_1714_, lean_object* v_b_1715_, lean_object* v_a_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1714_, v_b_1715_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(lean_object* v_as_1721_, lean_object* v_as_x27_1722_, lean_object* v_b_1723_, lean_object* v_a_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(v_as_1721_, v_as_x27_1722_, v_b_1723_, v_a_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v_as_x27_1722_);
lean_dec(v_as_1721_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(lean_object* v_msgData_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_1729_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_msgData_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l_Lean_Linter_List_indexLinter));
v___x_1741_ = l_Lean_Elab_Command_addLinter(v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(lean_object* v_e_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Lean_Expr_hasMVar(v_e_1802_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_e_1802_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v_mctx_1808_; lean_object* v___x_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; lean_object* v_cache_1813_; lean_object* v_zetaDeltaFVarIds_1814_; lean_object* v_postponed_1815_; lean_object* v_diag_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1825_; 
v___x_1807_ = lean_st_ref_get(v___y_1803_);
v_mctx_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_ref(v_mctx_1808_);
lean_dec(v___x_1807_);
v___x_1809_ = l_Lean_instantiateMVarsCore(v_mctx_1808_, v_e_1802_);
v_fst_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fst_1810_);
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1809_);
v___x_1812_ = lean_st_ref_take(v___y_1803_);
v_cache_1813_ = lean_ctor_get(v___x_1812_, 1);
v_zetaDeltaFVarIds_1814_ = lean_ctor_get(v___x_1812_, 2);
v_postponed_1815_ = lean_ctor_get(v___x_1812_, 3);
v_diag_1816_ = lean_ctor_get(v___x_1812_, 4);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1812_, 0);
lean_dec(v_unused_1826_);
v___x_1818_ = v___x_1812_;
v_isShared_1819_ = v_isSharedCheck_1825_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_diag_1816_);
lean_inc(v_postponed_1815_);
lean_inc(v_zetaDeltaFVarIds_1814_);
lean_inc(v_cache_1813_);
lean_dec(v___x_1812_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1825_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_snd_1811_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_snd_1811_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_cache_1813_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_zetaDeltaFVarIds_1814_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_postponed_1815_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_diag_1816_);
v___x_1821_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_st_ref_put(v___y_1803_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_fst_1810_);
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(lean_object* v_e_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1827_, v___y_1828_);
lean_dec(v___y_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1831_, v___y_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(lean_object* v_e_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(v_e_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_Linter_List_binders___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = ((lean_object*)(l_Lean_Linter_List_binders___lam__0___closed__1));
v___x_1850_ = l_Lean_Expr_const___override(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0(lean_object* v_expr_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___y_1858_; lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_saveState___redArg(v___y_1853_, v___y_1855_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
lean_inc(v___y_1855_);
lean_inc(v___y_1853_);
v___x_1863_ = lean_infer_type(v_expr_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_dec(v_a_1862_);
lean_dec(v___y_1855_);
v___y_1858_ = v___x_1863_;
goto v___jp_1857_;
}
else
{
lean_object* v_a_1864_; uint8_t v___y_1866_; uint8_t v___x_1878_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
v___x_1878_ = l_Lean_Exception_isInterrupt(v_a_1864_);
if (v___x_1878_ == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = l_Lean_Exception_isRuntime(v_a_1864_);
v___y_1866_ = v___x_1879_;
goto v___jp_1865_;
}
else
{
lean_dec(v_a_1864_);
v___y_1866_ = v___x_1878_;
goto v___jp_1865_;
}
v___jp_1865_:
{
if (v___y_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref_known(v___x_1863_, 1);
v___x_1867_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1862_, v___y_1853_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec(v_a_1862_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref_known(v___x_1867_, 1);
v___x_1868_ = lean_obj_once(&l_Lean_Linter_List_binders___lam__0___closed__2, &l_Lean_Linter_List_binders___lam__0___closed__2_once, _init_l_Lean_Linter_List_binders___lam__0___closed__2);
v___x_1869_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_1868_, v___y_1853_);
lean_dec(v___y_1853_);
return v___x_1869_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v___y_1853_);
v_a_1870_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1867_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1867_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_dec(v_a_1862_);
lean_dec(v___y_1855_);
v___y_1858_ = v___x_1863_;
goto v___jp_1857_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v_expr_1851_);
v_a_1880_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1861_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1861_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
v___jp_1857_:
{
if (lean_obj_tag(v___y_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___y_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___y_1858_, 1);
v___x_1860_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_a_1859_, v___y_1853_);
lean_dec(v___y_1853_);
return v___x_1860_;
}
else
{
lean_dec(v___y_1853_);
return v___y_1858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0___boxed(lean_object* v_expr_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Linter_List_binders___lam__0(v_expr_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1(lean_object* v_p_1895_, lean_object* v_ctx_1896_, lean_object* v_ti_1897_){
_start:
{
uint8_t v_isBinder_1899_; 
v_isBinder_1899_ = lean_ctor_get_uint8(v_ti_1897_, sizeof(void*)*4);
if (v_isBinder_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec_ref(v_ti_1897_);
lean_dec_ref(v_ctx_1896_);
lean_dec_ref(v_p_1895_);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v_toElabInfo_1902_; lean_object* v_lctx_1903_; lean_object* v_expr_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; 
v_toElabInfo_1902_ = lean_ctor_get(v_ti_1897_, 0);
lean_inc_ref(v_toElabInfo_1902_);
v_lctx_1903_ = lean_ctor_get(v_ti_1897_, 1);
lean_inc_ref_n(v_lctx_1903_, 2);
v_expr_1904_ = lean_ctor_get(v_ti_1897_, 3);
lean_inc_ref_n(v_expr_1904_, 2);
lean_dec_ref(v_ti_1897_);
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1905_, 0, v_expr_1904_);
v___x_1906_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1896_, v_lctx_1903_, v___f_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1950_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1950_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1950_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
lean_inc(v_a_1907_);
v___x_1911_ = l_Lean_Expr_cleanupAnnotations(v_a_1907_);
v___x_1912_ = lean_apply_1(v_p_1895_, v___x_1911_);
v___x_1913_ = lean_unbox(v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v_a_1907_);
lean_dec_ref(v_expr_1904_);
lean_dec_ref(v_lctx_1903_);
lean_dec_ref(v_toElabInfo_1902_);
v___x_1914_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1914_);
v___x_1916_ = v___x_1909_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
if (lean_obj_tag(v_expr_1904_) == 1)
{
lean_object* v_fvarId_1918_; lean_object* v___x_1919_; 
v_fvarId_1918_ = lean_ctor_get(v_expr_1904_, 0);
lean_inc(v_fvarId_1918_);
lean_dec_ref_known(v_expr_1904_, 1);
v___x_1919_ = lean_local_ctx_find(v_lctx_1903_, v_fvarId_1918_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v_a_1907_);
lean_dec_ref(v_toElabInfo_1902_);
v___x_1920_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1920_);
v___x_1922_ = v___x_1909_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
else
{
lean_object* v_val_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1945_; 
v_val_1924_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1926_ = v___x_1919_;
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_val_1924_);
lean_dec(v___x_1919_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_stx_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1943_; 
v_stx_1928_ = lean_ctor_get(v_toElabInfo_1902_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_toElabInfo_1902_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_toElabInfo_1902_, 0);
lean_dec(v_unused_1944_);
v___x_1930_ = v_toElabInfo_1902_;
v_isShared_1931_ = v_isSharedCheck_1943_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_stx_1928_);
lean_dec(v_toElabInfo_1902_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1943_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_LocalDecl_userName(v_val_1924_);
lean_dec(v_val_1924_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_a_1907_);
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_a_1907_);
v___x_1934_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_stx_1928_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1935_);
v___x_1937_ = v___x_1926_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1937_);
v___x_1939_ = v___x_1909_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec(v_a_1907_);
lean_dec_ref(v_expr_1904_);
lean_dec_ref(v_lctx_1903_);
lean_dec_ref(v_toElabInfo_1902_);
v___x_1946_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1946_);
v___x_1948_ = v___x_1909_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_expr_1904_);
lean_dec_ref(v_lctx_1903_);
lean_dec_ref(v_toElabInfo_1902_);
lean_dec_ref(v_p_1895_);
v_a_1951_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1906_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1906_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1___boxed(lean_object* v_p_1959_, lean_object* v_ctx_1960_, lean_object* v_ti_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Linter_List_binders___lam__1(v_p_1959_, v_ctx_1960_, v_ti_1961_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1965_, lean_object* v___x_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
if (lean_obj_tag(v_x_1967_) == 0)
{
lean_object* v_cs_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_cs_1970_ = lean_ctor_get(v_x_1967_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1972_ = v_x_1967_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_cs_1970_);
lean_dec(v_x_1967_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_cs_1970_);
v___x_1976_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v_cs_1970_);
lean_dec(v___x_1966_);
lean_dec_ref(v_f_1965_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_x_1968_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_x_1968_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
lean_del_object(v___x_1972_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_of_nat(v___x_1975_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_1965_, v___x_1966_, v_cs_1970_, v___x_1980_, v___x_1981_, v_x_1968_);
lean_dec_ref(v_cs_1970_);
return v___x_1982_;
}
}
}
else
{
lean_object* v_vs_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1997_; 
v_vs_1984_ = lean_ctor_get(v_x_1967_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1986_ = v_x_1967_;
v_isShared_1987_ = v_isSharedCheck_1997_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_vs_1984_);
lean_dec(v_x_1967_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1997_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_array_get_size(v_vs_1984_);
v___x_1990_ = lean_nat_dec_lt(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref(v_vs_1984_);
lean_dec(v___x_1966_);
lean_dec_ref(v_f_1965_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 0);
lean_ctor_set(v___x_1986_, 0, v_x_1968_);
v___x_1992_ = v___x_1986_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_x_1968_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
lean_del_object(v___x_1986_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1989_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1965_, v___x_1966_, v_vs_1984_, v___x_1994_, v___x_1995_, v_x_1968_);
lean_dec_ref(v_vs_1984_);
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_f_1998_, lean_object* v___x_1999_, lean_object* v_as_2000_, size_t v_i_2001_, size_t v_stop_2002_, lean_object* v_b_2003_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_eq(v_i_2001_, v_stop_2002_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_array_uget_borrowed(v_as_2000_, v_i_2001_);
lean_inc(v___x_2006_);
lean_inc(v___x_1999_);
lean_inc_ref(v_f_1998_);
v___x_2007_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1998_, v___x_1999_, v___x_2006_, v_b_2003_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; size_t v___x_2009_; size_t v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_2001_, v___x_2009_);
v_i_2001_ = v___x_2010_;
v_b_2003_ = v_a_2008_;
goto _start;
}
else
{
lean_dec(v___x_1999_);
lean_dec_ref(v_f_1998_);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v___x_1999_);
lean_dec_ref(v_f_1998_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_b_2003_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_f_2013_, lean_object* v___x_2014_, lean_object* v_x_2015_, size_t v_x_2016_, size_t v_x_2017_, lean_object* v_x_2018_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
lean_object* v_cs_2020_; lean_object* v___x_2021_; size_t v___x_2022_; lean_object* v_j_2023_; lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v_cs_2020_ = lean_ctor_get(v_x_2015_, 0);
lean_inc_ref(v_cs_2020_);
lean_dec_ref_known(v_x_2015_, 1);
v___x_2021_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2022_ = lean_usize_shift_right(v_x_2016_, v_x_2017_);
v_j_2023_ = lean_usize_to_nat(v___x_2022_);
v___x_2024_ = lean_array_get_borrowed(v___x_2021_, v_cs_2020_, v_j_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_shift_left(v___x_2025_, v_x_2017_);
v___x_2027_ = lean_usize_sub(v___x_2026_, v___x_2025_);
v___x_2028_ = lean_usize_land(v_x_2016_, v___x_2027_);
v___x_2029_ = ((size_t)5ULL);
v___x_2030_ = lean_usize_sub(v_x_2017_, v___x_2029_);
lean_inc(v___x_2024_);
lean_inc(v___x_2014_);
lean_inc_ref(v_f_2013_);
v___x_2031_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2013_, v___x_2014_, v___x_2024_, v___x_2028_, v___x_2030_, v_x_2018_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_add(v_j_2023_, v___x_2033_);
lean_dec(v_j_2023_);
v___x_2035_ = lean_array_get_size(v_cs_2020_);
v___x_2036_ = lean_nat_dec_lt(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_dec(v___x_2034_);
lean_dec(v_a_2032_);
lean_dec_ref(v_cs_2020_);
lean_dec(v___x_2014_);
lean_dec_ref(v_f_2013_);
return v___x_2031_;
}
else
{
size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref_known(v___x_2031_, 1);
v___x_2037_ = lean_usize_of_nat(v___x_2034_);
lean_dec(v___x_2034_);
v___x_2038_ = lean_usize_of_nat(v___x_2035_);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2013_, v___x_2014_, v_cs_2020_, v___x_2037_, v___x_2038_, v_a_2032_);
lean_dec_ref(v_cs_2020_);
return v___x_2039_;
}
}
else
{
lean_dec(v_j_2023_);
lean_dec_ref(v_cs_2020_);
lean_dec(v___x_2014_);
lean_dec_ref(v_f_2013_);
return v___x_2031_;
}
}
else
{
lean_object* v_vs_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2053_; 
v_vs_2040_ = lean_ctor_get(v_x_2015_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2042_ = v_x_2015_;
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_vs_2040_);
lean_dec(v_x_2015_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_usize_to_nat(v_x_2016_);
v___x_2045_ = lean_array_get_size(v_vs_2040_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v___x_2044_);
lean_dec_ref(v_vs_2040_);
lean_dec(v___x_2014_);
lean_dec_ref(v_f_2013_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 0);
lean_ctor_set(v___x_2042_, 0, v_x_2018_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_x_2018_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2042_);
v___x_2050_ = lean_usize_of_nat(v___x_2044_);
lean_dec(v___x_2044_);
v___x_2051_ = lean_usize_of_nat(v___x_2045_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2013_, v___x_2014_, v_vs_2040_, v___x_2050_, v___x_2051_, v_x_2018_);
lean_dec_ref(v_vs_2040_);
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_2054_, lean_object* v___x_2055_, lean_object* v_t_2056_, lean_object* v_init_2057_, lean_object* v_start_2058_){
_start:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_nat_dec_eq(v_start_2058_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v_root_2062_; lean_object* v_tail_2063_; size_t v_shift_2064_; lean_object* v_tailOff_2065_; uint8_t v___x_2066_; 
v_root_2062_ = lean_ctor_get(v_t_2056_, 0);
lean_inc_ref(v_root_2062_);
v_tail_2063_ = lean_ctor_get(v_t_2056_, 1);
lean_inc_ref(v_tail_2063_);
v_shift_2064_ = lean_ctor_get_usize(v_t_2056_, 4);
v_tailOff_2065_ = lean_ctor_get(v_t_2056_, 3);
lean_inc(v_tailOff_2065_);
lean_dec_ref(v_t_2056_);
v___x_2066_ = lean_nat_dec_le(v_tailOff_2065_, v_start_2058_);
if (v___x_2066_ == 0)
{
size_t v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_tailOff_2065_);
v___x_2067_ = lean_usize_of_nat(v_start_2058_);
lean_inc(v___x_2055_);
lean_inc_ref(v_f_2054_);
v___x_2068_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2054_, v___x_2055_, v_root_2062_, v___x_2067_, v_shift_2064_, v_init_2057_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
v___x_2070_ = lean_array_get_size(v_tail_2063_);
v___x_2071_ = lean_nat_dec_lt(v___x_2060_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_a_2069_);
lean_dec_ref(v_tail_2063_);
lean_dec(v___x_2055_);
lean_dec_ref(v_f_2054_);
return v___x_2068_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref_known(v___x_2068_, 1);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_of_nat(v___x_2070_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2054_, v___x_2055_, v_tail_2063_, v___x_2072_, v___x_2073_, v_a_2069_);
lean_dec_ref(v_tail_2063_);
return v___x_2074_;
}
}
else
{
lean_dec_ref(v_tail_2063_);
lean_dec(v___x_2055_);
lean_dec_ref(v_f_2054_);
return v___x_2068_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
lean_dec_ref(v_root_2062_);
v___x_2075_ = lean_nat_sub(v_start_2058_, v_tailOff_2065_);
lean_dec(v_tailOff_2065_);
v___x_2076_ = lean_array_get_size(v_tail_2063_);
v___x_2077_ = lean_nat_dec_lt(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v___x_2075_);
lean_dec_ref(v_tail_2063_);
lean_dec(v___x_2055_);
lean_dec_ref(v_f_2054_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_init_2057_);
return v___x_2078_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_usize_of_nat(v___x_2075_);
lean_dec(v___x_2075_);
v___x_2080_ = lean_usize_of_nat(v___x_2076_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2054_, v___x_2055_, v_tail_2063_, v___x_2079_, v___x_2080_, v_init_2057_);
lean_dec_ref(v_tail_2063_);
return v___x_2081_;
}
}
}
else
{
lean_object* v_root_2082_; lean_object* v_tail_2083_; lean_object* v___x_2084_; 
v_root_2082_ = lean_ctor_get(v_t_2056_, 0);
lean_inc_ref(v_root_2082_);
v_tail_2083_ = lean_ctor_get(v_t_2056_, 1);
lean_inc_ref(v_tail_2083_);
lean_dec_ref(v_t_2056_);
lean_inc(v___x_2055_);
lean_inc_ref(v_f_2054_);
v___x_2084_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2054_, v___x_2055_, v_root_2082_, v_init_2057_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
v___x_2086_ = lean_array_get_size(v_tail_2083_);
v___x_2087_ = lean_nat_dec_lt(v___x_2060_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec(v_a_2085_);
lean_dec_ref(v_tail_2083_);
lean_dec(v___x_2055_);
lean_dec_ref(v_f_2054_);
return v___x_2084_;
}
else
{
size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = lean_usize_of_nat(v___x_2086_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2054_, v___x_2055_, v_tail_2083_, v___x_2088_, v___x_2089_, v_a_2085_);
lean_dec_ref(v_tail_2083_);
return v___x_2090_;
}
}
else
{
lean_dec_ref(v_tail_2083_);
lean_dec(v___x_2055_);
lean_dec_ref(v_f_2054_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2091_, lean_object* v_ctx_x3f_2092_, lean_object* v_a_2093_, lean_object* v_x_2094_){
_start:
{
switch(lean_obj_tag(v_x_2094_))
{
case 0:
{
lean_object* v_i_2096_; lean_object* v_t_2097_; lean_object* v___x_2098_; 
v_i_2096_ = lean_ctor_get(v_x_2094_, 0);
lean_inc_ref(v_i_2096_);
v_t_2097_ = lean_ctor_get(v_x_2094_, 1);
lean_inc_ref(v_t_2097_);
lean_dec_ref_known(v_x_2094_, 2);
v___x_2098_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2096_, v_ctx_x3f_2092_);
v_ctx_x3f_2092_ = v___x_2098_;
v_x_2094_ = v_t_2097_;
goto _start;
}
case 1:
{
lean_object* v_i_2100_; lean_object* v_children_2101_; lean_object* v_a_2103_; 
v_i_2100_ = lean_ctor_get(v_x_2094_, 0);
lean_inc_ref(v_i_2100_);
v_children_2101_ = lean_ctor_get(v_x_2094_, 1);
lean_inc_ref(v_children_2101_);
lean_dec_ref_known(v_x_2094_, 2);
if (lean_obj_tag(v_ctx_x3f_2092_) == 0)
{
v_a_2103_ = v_a_2093_;
goto v___jp_2102_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2108_; 
v_val_2107_ = lean_ctor_get(v_ctx_x3f_2092_, 0);
lean_inc_ref(v_f_2091_);
lean_inc_ref(v_i_2100_);
lean_inc(v_val_2107_);
v___x_2108_ = lean_apply_4(v_f_2091_, v_val_2107_, v_i_2100_, v_a_2093_, lean_box(0));
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_a_2103_ = v_a_2109_;
goto v___jp_2102_;
}
else
{
lean_dec_ref_known(v_ctx_x3f_2092_, 1);
lean_dec_ref(v_children_2101_);
lean_dec_ref(v_i_2100_);
lean_dec_ref(v_f_2091_);
return v___x_2108_;
}
}
v___jp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2092_, v_i_2100_);
lean_dec_ref(v_i_2100_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2091_, v___x_2104_, v_children_2101_, v_a_2103_, v___x_2105_);
return v___x_2106_;
}
}
default: 
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_ctx_x3f_2092_);
lean_dec_ref(v_f_2091_);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_x_2094_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v_x_2094_, 0);
lean_dec(v_unused_2117_);
v___x_2111_ = v_x_2094_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v_x_2094_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set_tag(v___x_2111_, 0);
lean_ctor_set(v___x_2111_, 0, v_a_2093_);
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2093_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2118_, lean_object* v___x_2119_, lean_object* v_as_2120_, size_t v_i_2121_, size_t v_stop_2122_, lean_object* v_b_2123_){
_start:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_eq(v_i_2121_, v_stop_2122_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_array_uget_borrowed(v_as_2120_, v_i_2121_);
lean_inc(v___x_2126_);
lean_inc(v___x_2119_);
lean_inc_ref(v_f_2118_);
v___x_2127_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2118_, v___x_2119_, v_b_2123_, v___x_2126_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; size_t v___x_2129_; size_t v___x_2130_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_add(v_i_2121_, v___x_2129_);
v_i_2121_ = v___x_2130_;
v_b_2123_ = v_a_2128_;
goto _start;
}
else
{
lean_dec(v___x_2119_);
lean_dec_ref(v_f_2118_);
return v___x_2127_;
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v___x_2119_);
lean_dec_ref(v_f_2118_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_b_2123_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_2133_, lean_object* v___x_2134_, lean_object* v_as_2135_, lean_object* v_i_2136_, lean_object* v_stop_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_){
_start:
{
size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; lean_object* v_res_2142_; 
v_i_boxed_2140_ = lean_unbox_usize(v_i_2136_);
lean_dec(v_i_2136_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2137_);
lean_dec(v_stop_2137_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2133_, v___x_2134_, v_as_2135_, v_i_boxed_2140_, v_stop_boxed_2141_, v_b_2138_);
lean_dec_ref(v_as_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_2143_, lean_object* v___x_2144_, lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_){
_start:
{
size_t v_i_boxed_2150_; size_t v_stop_boxed_2151_; lean_object* v_res_2152_; 
v_i_boxed_2150_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2151_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2143_, v___x_2144_, v_as_2145_, v_i_boxed_2150_, v_stop_boxed_2151_, v_b_2148_);
lean_dec_ref(v_as_2145_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_2153_, lean_object* v_ctx_x3f_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2153_, v_ctx_x3f_2154_, v_a_2155_, v_x_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_2159_, lean_object* v___x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2159_, v___x_2160_, v_x_2161_, v_x_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_f_2165_, lean_object* v___x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v___y_2171_){
_start:
{
size_t v_x_2498__boxed_2172_; size_t v_x_2499__boxed_2173_; lean_object* v_res_2174_; 
v_x_2498__boxed_2172_ = lean_unbox_usize(v_x_2168_);
lean_dec(v_x_2168_);
v_x_2499__boxed_2173_ = lean_unbox_usize(v_x_2169_);
lean_dec(v_x_2169_);
v_res_2174_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2165_, v___x_2166_, v_x_2167_, v_x_2498__boxed_2172_, v_x_2499__boxed_2173_, v_x_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_2175_, lean_object* v___x_2176_, lean_object* v_t_2177_, lean_object* v_init_2178_, lean_object* v_start_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2175_, v___x_2176_, v_t_2177_, v_init_2178_, v_start_2179_);
lean_dec(v_start_2179_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(lean_object* v_f_2182_, lean_object* v_init_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2182_, v___x_2186_, v_init_2183_, v_x_2184_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(lean_object* v_f_2188_, lean_object* v_init_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2188_, v_init_2189_, v_x_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(lean_object* v_f_2193_, lean_object* v_ctx_2194_, lean_object* v_info_2195_, lean_object* v_result_2196_){
_start:
{
if (lean_obj_tag(v_info_2195_) == 1)
{
lean_object* v_i_2198_; lean_object* v___x_2199_; 
v_i_2198_ = lean_ctor_get(v_info_2195_, 0);
lean_inc_ref(v_i_2198_);
lean_dec_ref_known(v_info_2195_, 1);
v___x_2199_ = lean_apply_3(v_f_2193_, v_ctx_2194_, v_i_2198_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2212_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
if (lean_obj_tag(v_a_2200_) == 0)
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_result_2196_);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_result_2196_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v_val_2207_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v_a_2200_, 1);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_val_2207_);
lean_ctor_set(v___x_2208_, 1, v_result_2196_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2208_);
v___x_2210_ = v___x_2202_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_result_2196_);
v_a_2213_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2199_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2199_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v___x_2221_; 
lean_dec_ref(v_info_2195_);
lean_dec_ref(v_ctx_2194_);
lean_dec_ref(v_f_2193_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_result_2196_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(lean_object* v_f_2222_, lean_object* v_ctx_2223_, lean_object* v_info_2224_, lean_object* v_result_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_2222_, v_ctx_2223_, v_info_2224_, v_result_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(lean_object* v_t_2228_, lean_object* v_f_2229_){
_start:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2231_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2231_, 0, v_f_2229_);
v___x_2232_ = lean_box(0);
v___x_2233_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_2231_, v___x_2232_, v_t_2228_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(lean_object* v_t_2234_, lean_object* v_f_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2234_, v_f_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders(lean_object* v_t_2238_, lean_object* v_p_2239_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; 
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2241_, 0, v_p_2239_);
v___x_2242_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2238_, v___f_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___boxed(lean_object* v_t_2243_, lean_object* v_p_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Linter_List_binders(v_t_2243_, v_p_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_object* v_00_u03b1_2247_, lean_object* v_t_2248_, lean_object* v_f_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2248_, v_f_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(lean_object* v_00_u03b1_2252_, lean_object* v_t_2253_, lean_object* v_f_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(v_00_u03b1_2252_, v_t_2253_, v_f_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_object* v_00_u03b1_2257_, lean_object* v_f_2258_, lean_object* v_init_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2258_, v_init_2259_, v_x_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_f_2264_, lean_object* v_init_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_2263_, v_f_2264_, v_init_2265_, v_x_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_2269_, lean_object* v_f_2270_, lean_object* v_ctx_x3f_2271_, lean_object* v_a_2272_, lean_object* v_x_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2270_, v_ctx_x3f_2271_, v_a_2272_, v_x_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_f_2277_, lean_object* v_ctx_x3f_2278_, lean_object* v_a_2279_, lean_object* v_x_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_2276_, v_f_2277_, v_ctx_x3f_2278_, v_a_2279_, v_x_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2283_, lean_object* v_f_2284_, lean_object* v___x_2285_, lean_object* v_t_2286_, lean_object* v_init_2287_, lean_object* v_start_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2284_, v___x_2285_, v_t_2286_, v_init_2287_, v_start_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_f_2292_, lean_object* v___x_2293_, lean_object* v_t_2294_, lean_object* v_init_2295_, lean_object* v_start_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_2291_, v_f_2292_, v___x_2293_, v_t_2294_, v_init_2295_, v_start_2296_);
lean_dec(v_start_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2299_, lean_object* v_f_2300_, lean_object* v___x_2301_, lean_object* v_x_2302_, size_t v_x_2303_, size_t v_x_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2300_, v___x_2301_, v_x_2302_, v_x_2303_, v_x_2304_, v_x_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_f_2309_, lean_object* v___x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_){
_start:
{
size_t v_x_2852__boxed_2316_; size_t v_x_2853__boxed_2317_; lean_object* v_res_2318_; 
v_x_2852__boxed_2316_ = lean_unbox_usize(v_x_2312_);
lean_dec(v_x_2312_);
v_x_2853__boxed_2317_ = lean_unbox_usize(v_x_2313_);
lean_dec(v_x_2313_);
v_res_2318_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_2308_, v_f_2309_, v___x_2310_, v_x_2311_, v_x_2852__boxed_2316_, v_x_2853__boxed_2317_, v_x_2314_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2319_, lean_object* v_f_2320_, lean_object* v___x_2321_, lean_object* v_as_2322_, size_t v_i_2323_, size_t v_stop_2324_, lean_object* v_b_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2320_, v___x_2321_, v_as_2322_, v_i_2323_, v_stop_2324_, v_b_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_f_2329_, lean_object* v___x_2330_, lean_object* v_as_2331_, lean_object* v_i_2332_, lean_object* v_stop_2333_, lean_object* v_b_2334_, lean_object* v___y_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; lean_object* v_res_2338_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2332_);
lean_dec(v_i_2332_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2333_);
lean_dec(v_stop_2333_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2328_, v_f_2329_, v___x_2330_, v_as_2331_, v_i_boxed_2336_, v_stop_boxed_2337_, v_b_2334_);
lean_dec_ref(v_as_2331_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_2339_, lean_object* v_f_2340_, lean_object* v___x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2340_, v___x_2341_, v_x_2342_, v_x_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_f_2347_, lean_object* v___x_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_2346_, v_f_2347_, v___x_2348_, v_x_2349_, v_x_2350_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_2353_, lean_object* v_f_2354_, lean_object* v___x_2355_, lean_object* v_as_2356_, size_t v_i_2357_, size_t v_stop_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2354_, v___x_2355_, v_as_2356_, v_i_2357_, v_stop_2358_, v_b_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2362_, lean_object* v_f_2363_, lean_object* v___x_2364_, lean_object* v_as_2365_, lean_object* v_i_2366_, lean_object* v_stop_2367_, lean_object* v_b_2368_, lean_object* v___y_2369_){
_start:
{
size_t v_i_boxed_2370_; size_t v_stop_boxed_2371_; lean_object* v_res_2372_; 
v_i_boxed_2370_ = lean_unbox_usize(v_i_2366_);
lean_dec(v_i_2366_);
v_stop_boxed_2371_ = lean_unbox_usize(v_stop_2367_);
lean_dec(v_stop_2367_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_2362_, v_f_2363_, v___x_2364_, v_as_2365_, v_i_boxed_2370_, v_stop_boxed_2371_, v_b_2368_);
lean_dec_ref(v_as_2365_);
return v_res_2372_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(lean_object* v_as_x27_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
if (lean_obj_tag(v_as_x27_2379_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_b_2380_);
return v___x_2384_;
}
else
{
lean_object* v_head_2385_; lean_object* v_snd_2386_; lean_object* v_tail_2387_; lean_object* v_fst_2388_; lean_object* v_fst_2389_; lean_object* v_snd_2390_; lean_object* v___x_2391_; 
v_head_2385_ = lean_ctor_get(v_as_x27_2379_, 0);
v_snd_2386_ = lean_ctor_get(v_head_2385_, 1);
v_tail_2387_ = lean_ctor_get(v_as_x27_2379_, 1);
v_fst_2388_ = lean_ctor_get(v_head_2385_, 0);
v_fst_2389_ = lean_ctor_get(v_snd_2386_, 0);
v_snd_2390_ = lean_ctor_get(v_snd_2386_, 1);
v___x_2391_ = lean_box(0);
if (lean_obj_tag(v_fst_2389_) == 1)
{
lean_object* v_str_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_str_2392_ = lean_ctor_get(v_fst_2389_, 1);
lean_inc_ref(v_str_2392_);
v___x_2393_ = l_Lean_Linter_List_stripBinderName(v_str_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Linter_List_allowedArrayNames));
v___x_2395_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2396_ = l_Lean_Linter_List_linter_listVariables;
v___x_2407_ = l_Lean_Expr_getAppNumArgs(v_snd_2390_);
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_sub(v___x_2407_, v___x_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = l_Lean_Expr_getRevArg_x21(v_snd_2390_, v___x_2409_);
v___x_2411_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2412_ = l_Lean_Expr_isAppOf(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2414_ = l_Lean_Expr_isAppOf(v___x_2410_, v___x_2413_);
lean_dec_ref(v___x_2410_);
if (v___x_2414_ == 0)
{
goto v___jp_2397_;
}
else
{
goto v___jp_2403_;
}
}
else
{
lean_dec_ref(v___x_2410_);
goto v___jp_2403_;
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2398_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
v___x_2399_ = l_Lean_stringToMessageData(v___x_2393_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
lean_inc(v_fst_2388_);
v___x_2401_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2396_, v_fst_2388_, v___x_2400_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_dec_ref_known(v___x_2401_, 1);
v_as_x27_2379_ = v_tail_2387_;
v_b_2380_ = v___x_2391_;
goto _start;
}
else
{
return v___x_2401_;
}
}
v___jp_2403_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2405_ = lean_string_dec_eq(v___x_2393_, v___x_2404_);
if (v___x_2405_ == 0)
{
goto v___jp_2397_;
}
else
{
lean_dec_ref(v___x_2393_);
v_as_x27_2379_ = v_tail_2387_;
v_b_2380_ = v___x_2391_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2393_);
v_as_x27_2379_ = v_tail_2387_;
v_b_2380_ = v___x_2391_;
goto _start;
}
}
else
{
v_as_x27_2379_ = v_tail_2387_;
v_b_2380_ = v___x_2391_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(lean_object* v_as_x27_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_2417_, v_b_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v_as_x27_2417_);
return v_res_2422_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(lean_object* v_as_x27_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
if (lean_obj_tag(v_as_x27_2429_) == 0)
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_b_2430_);
return v___x_2434_;
}
else
{
lean_object* v_head_2435_; lean_object* v_snd_2436_; lean_object* v_tail_2437_; lean_object* v_fst_2438_; lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v___x_2441_; 
v_head_2435_ = lean_ctor_get(v_as_x27_2429_, 0);
v_snd_2436_ = lean_ctor_get(v_head_2435_, 1);
v_tail_2437_ = lean_ctor_get(v_as_x27_2429_, 1);
v_fst_2438_ = lean_ctor_get(v_head_2435_, 0);
v_fst_2439_ = lean_ctor_get(v_snd_2436_, 0);
v_snd_2440_ = lean_ctor_get(v_snd_2436_, 1);
v___x_2441_ = lean_box(0);
if (lean_obj_tag(v_fst_2439_) == 1)
{
lean_object* v_str_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_str_2442_ = lean_ctor_get(v_fst_2439_, 1);
lean_inc_ref(v_str_2442_);
v___x_2443_ = l_Lean_Linter_List_stripBinderName(v_str_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_Linter_List_allowedListNames));
v___x_2445_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2443_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2446_ = l_Lean_Linter_List_linter_listVariables;
v___x_2460_ = l_Lean_Expr_getAppNumArgs(v_snd_2440_);
v___x_2461_ = lean_unsigned_to_nat(1u);
v___x_2462_ = lean_nat_sub(v___x_2460_, v___x_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = l_Lean_Expr_getRevArg_x21(v_snd_2440_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2465_ = l_Lean_Expr_isAppOf(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2467_ = l_Lean_Expr_isAppOf(v___x_2463_, v___x_2466_);
lean_dec_ref(v___x_2463_);
if (v___x_2467_ == 0)
{
goto v___jp_2447_;
}
else
{
goto v___jp_2453_;
}
}
else
{
lean_dec_ref(v___x_2463_);
goto v___jp_2453_;
}
v___jp_2447_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2448_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
v___x_2449_ = l_Lean_stringToMessageData(v___x_2443_);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
lean_inc(v_fst_2438_);
v___x_2451_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2446_, v_fst_2438_, v___x_2450_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref_known(v___x_2451_, 1);
v_as_x27_2429_ = v_tail_2437_;
v_b_2430_ = v___x_2441_;
goto _start;
}
else
{
return v___x_2451_;
}
}
v___jp_2453_:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2));
v___x_2455_ = lean_string_dec_eq(v___x_2443_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2457_ = lean_string_dec_eq(v___x_2443_, v___x_2456_);
if (v___x_2457_ == 0)
{
goto v___jp_2447_;
}
else
{
lean_dec_ref(v___x_2443_);
v_as_x27_2429_ = v_tail_2437_;
v_b_2430_ = v___x_2441_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2443_);
v_as_x27_2429_ = v_tail_2437_;
v_b_2430_ = v___x_2441_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2443_);
v_as_x27_2429_ = v_tail_2437_;
v_b_2430_ = v___x_2441_;
goto _start;
}
}
else
{
v_as_x27_2429_ = v_tail_2437_;
v_b_2430_ = v___x_2441_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(lean_object* v_as_x27_2470_, lean_object* v_b_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_2470_, v_b_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v_as_x27_2470_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
if (lean_obj_tag(v_a_2476_) == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = l_List_reverse___redArg(v_a_2477_);
return v___x_2478_;
}
else
{
lean_object* v_head_2479_; lean_object* v_snd_2480_; lean_object* v_tail_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2493_; 
v_head_2479_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_head_2479_);
v_snd_2480_ = lean_ctor_get(v_head_2479_, 1);
v_tail_2481_ = lean_ctor_get(v_a_2476_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_a_2476_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_a_2476_, 0);
lean_dec(v_unused_2494_);
v___x_2483_ = v_a_2476_;
v_isShared_2484_ = v_isSharedCheck_2493_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_tail_2481_);
lean_dec(v_a_2476_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2493_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_snd_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_snd_2485_ = lean_ctor_get(v_snd_2480_, 1);
v___x_2486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2487_ = l_Lean_Expr_isAppOf(v_snd_2485_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_del_object(v___x_2483_);
lean_dec(v_head_2479_);
v_a_2476_ = v_tail_2481_;
goto _start;
}
else
{
lean_object* v___x_2490_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 1, v_a_2477_);
v___x_2490_ = v___x_2483_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_head_2479_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_a_2477_);
v___x_2490_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
v_a_2476_ = v_tail_2481_;
v_a_2477_ = v___x_2490_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(uint8_t v___x_2495_, lean_object* v_x_2496_){
_start:
{
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(lean_object* v___x_2497_, lean_object* v_x_2498_){
_start:
{
uint8_t v___x_12937__boxed_2499_; uint8_t v_res_2500_; lean_object* v_r_2501_; 
v___x_12937__boxed_2499_ = lean_unbox(v___x_2497_);
v_res_2500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v___x_12937__boxed_2499_, v_x_2498_);
lean_dec_ref(v_x_2498_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
if (lean_obj_tag(v_a_2502_) == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = l_List_reverse___redArg(v_a_2503_);
return v___x_2504_;
}
else
{
lean_object* v_head_2505_; lean_object* v_snd_2506_; lean_object* v_tail_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2519_; 
v_head_2505_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_head_2505_);
v_snd_2506_ = lean_ctor_get(v_head_2505_, 1);
v_tail_2507_ = lean_ctor_get(v_a_2502_, 1);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_a_2502_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v_a_2502_, 0);
lean_dec(v_unused_2520_);
v___x_2509_ = v_a_2502_;
v_isShared_2510_ = v_isSharedCheck_2519_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_tail_2507_);
lean_dec(v_a_2502_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2519_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_snd_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_snd_2511_ = lean_ctor_get(v_snd_2506_, 1);
v___x_2512_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2513_ = l_Lean_Expr_isAppOf(v_snd_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_del_object(v___x_2509_);
lean_dec(v_head_2505_);
v_a_2502_ = v_tail_2507_;
goto _start;
}
else
{
lean_object* v___x_2516_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_a_2503_);
v___x_2516_ = v___x_2509_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_head_2505_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_a_2503_);
v___x_2516_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
v_a_2502_ = v_tail_2507_;
v_a_2503_ = v___x_2516_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(lean_object* v_as_x27_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
if (lean_obj_tag(v_as_x27_2524_) == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2525_);
return v___x_2529_;
}
else
{
lean_object* v_head_2530_; lean_object* v_snd_2531_; lean_object* v_tail_2532_; lean_object* v_fst_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; 
v_head_2530_ = lean_ctor_get(v_as_x27_2524_, 0);
v_snd_2531_ = lean_ctor_get(v_head_2530_, 1);
v_tail_2532_ = lean_ctor_get(v_as_x27_2524_, 1);
v_fst_2533_ = lean_ctor_get(v_head_2530_, 0);
v_fst_2534_ = lean_ctor_get(v_snd_2531_, 0);
v_snd_2535_ = lean_ctor_get(v_snd_2531_, 1);
v___x_2536_ = lean_box(0);
if (lean_obj_tag(v_fst_2534_) == 1)
{
lean_object* v_str_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_str_2537_ = lean_ctor_get(v_fst_2534_, 1);
lean_inc_ref(v_str_2537_);
v___x_2538_ = l_Lean_Linter_List_stripBinderName(v_str_2537_);
v___x_2539_ = ((lean_object*)(l_Lean_Linter_List_allowedVectorNames));
v___x_2540_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2541_ = l_Lean_Linter_List_linter_listVariables;
v___x_2548_ = l_Lean_Expr_getAppNumArgs(v_snd_2535_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_sub(v___x_2548_, v___x_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = l_Lean_Expr_getRevArg_x21(v_snd_2535_, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2553_ = l_Lean_Expr_isAppOf(v___x_2551_, v___x_2552_);
lean_dec_ref(v___x_2551_);
if (v___x_2553_ == 0)
{
goto v___jp_2542_;
}
else
{
lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2555_ = lean_string_dec_eq(v___x_2538_, v___x_2554_);
if (v___x_2555_ == 0)
{
goto v___jp_2542_;
}
else
{
lean_dec_ref(v___x_2538_);
v_as_x27_2524_ = v_tail_2532_;
v_b_2525_ = v___x_2536_;
goto _start;
}
}
v___jp_2542_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2543_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
v___x_2544_ = l_Lean_stringToMessageData(v___x_2538_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
lean_inc(v_fst_2533_);
v___x_2546_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2541_, v_fst_2533_, v___x_2545_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref_known(v___x_2546_, 1);
v_as_x27_2524_ = v_tail_2532_;
v_b_2525_ = v___x_2536_;
goto _start;
}
else
{
return v___x_2546_;
}
}
}
else
{
lean_dec_ref(v___x_2538_);
v_as_x27_2524_ = v_tail_2532_;
v_b_2525_ = v___x_2536_;
goto _start;
}
}
else
{
v_as_x27_2524_ = v_tail_2532_;
v_b_2525_ = v___x_2536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(lean_object* v_as_x27_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_2559_, v_b_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v_as_x27_2559_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
if (lean_obj_tag(v_a_2565_) == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = l_List_reverse___redArg(v_a_2566_);
return v___x_2567_;
}
else
{
lean_object* v_head_2568_; lean_object* v_snd_2569_; lean_object* v_tail_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2582_; 
v_head_2568_ = lean_ctor_get(v_a_2565_, 0);
lean_inc(v_head_2568_);
v_snd_2569_ = lean_ctor_get(v_head_2568_, 1);
v_tail_2570_ = lean_ctor_get(v_a_2565_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_a_2565_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v_a_2565_, 0);
lean_dec(v_unused_2583_);
v___x_2572_ = v_a_2565_;
v_isShared_2573_ = v_isSharedCheck_2582_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_tail_2570_);
lean_dec(v_a_2565_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2582_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_snd_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_snd_2574_ = lean_ctor_get(v_snd_2569_, 1);
v___x_2575_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2576_ = l_Lean_Expr_isAppOf(v_snd_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_del_object(v___x_2572_);
lean_dec(v_head_2568_);
v_a_2565_ = v_tail_2570_;
goto _start;
}
else
{
lean_object* v___x_2579_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v_a_2566_);
v___x_2579_ = v___x_2572_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_head_2568_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_a_2566_);
v___x_2579_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
v_a_2565_ = v_tail_2570_;
v_a_2566_ = v___x_2579_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(uint8_t v___x_2584_, lean_object* v_as_2585_, size_t v_sz_2586_, size_t v_i_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_usize_dec_lt(v_i_2587_, v_sz_2586_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_b_2588_);
return v___x_2593_;
}
else
{
lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v_a_2596_; lean_object* v___x_2597_; 
lean_dec_ref(v_b_2588_);
v___x_2594_ = lean_box(v___x_2584_);
v___f_2595_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2595_, 0, v___x_2594_);
v_a_2596_ = lean_array_uget_borrowed(v_as_2585_, v_i_2587_);
lean_inc(v_a_2596_);
v___x_2597_ = l_Lean_Linter_List_binders(v_a_2596_, v___f_2595_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_n(v_a_2598_, 2);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2598_, v___x_2600_);
v___x_2602_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2601_, v___x_2599_, v___y_2589_, v___y_2590_);
lean_dec(v___x_2601_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref_known(v___x_2602_, 1);
lean_inc(v_a_2598_);
v___x_2603_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2598_, v___x_2600_);
v___x_2604_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2603_, v___x_2599_, v___y_2589_, v___y_2590_);
lean_dec(v___x_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref_known(v___x_2604_, 1);
v___x_2605_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2598_, v___x_2600_);
v___x_2606_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2605_, v___x_2599_, v___y_2589_, v___y_2590_);
lean_dec(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; size_t v___x_2608_; size_t v___x_2609_; 
lean_dec_ref_known(v___x_2606_, 1);
v___x_2607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2608_ = ((size_t)1ULL);
v___x_2609_ = lean_usize_add(v_i_2587_, v___x_2608_);
v_i_2587_ = v___x_2609_;
v_b_2588_ = v___x_2607_;
goto _start;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2606_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2606_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2598_);
v_a_2619_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2604_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2604_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_a_2598_);
v_a_2627_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2602_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2602_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2647_; 
v_a_2635_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2637_ = v___x_2597_;
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2597_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_ref_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v_ref_2639_ = lean_ctor_get(v___y_2589_, 7);
v___x_2640_ = lean_io_error_to_string(v_a_2635_);
v___x_2641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
v___x_2642_ = l_Lean_MessageData_ofFormat(v___x_2641_);
lean_inc(v_ref_2639_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v_ref_2639_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2643_);
v___x_2645_ = v___x_2637_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(lean_object* v___x_2648_, lean_object* v_as_2649_, lean_object* v_sz_2650_, lean_object* v_i_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_13117__boxed_2656_; size_t v_sz_boxed_2657_; size_t v_i_boxed_2658_; lean_object* v_res_2659_; 
v___x_13117__boxed_2656_ = lean_unbox(v___x_2648_);
v_sz_boxed_2657_ = lean_unbox_usize(v_sz_2650_);
lean_dec(v_sz_2650_);
v_i_boxed_2658_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_13117__boxed_2656_, v_as_2649_, v_sz_boxed_2657_, v_i_boxed_2658_, v_b_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_as_2649_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(uint8_t v___x_2660_, lean_object* v_as_2661_, size_t v_sz_2662_, size_t v_i_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_usize_dec_lt(v_i_2663_, v_sz_2662_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_b_2664_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; lean_object* v___f_2671_; lean_object* v_a_2672_; lean_object* v___x_2673_; 
lean_dec_ref(v_b_2664_);
v___x_2670_ = lean_box(v___x_2660_);
v___f_2671_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2671_, 0, v___x_2670_);
v_a_2672_ = lean_array_uget_borrowed(v_as_2661_, v_i_2663_);
lean_inc(v_a_2672_);
v___x_2673_ = l_Lean_Linter_List_binders(v_a_2672_, v___f_2671_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc_n(v_a_2674_, 2);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_box(0);
v___x_2677_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2674_, v___x_2676_);
v___x_2678_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2677_, v___x_2675_, v___y_2665_, v___y_2666_);
lean_dec(v___x_2677_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2678_, 1);
lean_inc(v_a_2674_);
v___x_2679_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2674_, v___x_2676_);
v___x_2680_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2679_, v___x_2675_, v___y_2665_, v___y_2666_);
lean_dec(v___x_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec_ref_known(v___x_2680_, 1);
v___x_2681_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2674_, v___x_2676_);
v___x_2682_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2681_, v___x_2675_, v___y_2665_, v___y_2666_);
lean_dec(v___x_2681_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref_known(v___x_2682_, 1);
v___x_2683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2684_ = ((size_t)1ULL);
v___x_2685_ = lean_usize_add(v_i_2663_, v___x_2684_);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_2660_, v_as_2661_, v_sz_2662_, v___x_2685_, v___x_2683_, v___y_2665_, v___y_2666_);
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2682_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2682_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2674_);
v_a_2695_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2680_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2680_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2674_);
v_a_2703_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2678_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2678_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2723_; 
v_a_2711_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2713_ = v___x_2673_;
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2673_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_ref_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v_ref_2715_ = lean_ctor_get(v___y_2665_, 7);
v___x_2716_ = lean_io_error_to_string(v_a_2711_);
v___x_2717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
v___x_2718_ = l_Lean_MessageData_ofFormat(v___x_2717_);
lean_inc(v_ref_2715_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_ref_2715_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2719_);
v___x_2721_ = v___x_2713_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(lean_object* v___x_2724_, lean_object* v_as_2725_, lean_object* v_sz_2726_, lean_object* v_i_2727_, lean_object* v_b_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v___x_13244__boxed_2732_; size_t v_sz_boxed_2733_; size_t v_i_boxed_2734_; lean_object* v_res_2735_; 
v___x_13244__boxed_2732_ = lean_unbox(v___x_2724_);
v_sz_boxed_2733_ = lean_unbox_usize(v_sz_2726_);
lean_dec(v_sz_2726_);
v_i_boxed_2734_ = lean_unbox_usize(v_i_2727_);
lean_dec(v_i_2727_);
v_res_2735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_13244__boxed_2732_, v_as_2725_, v_sz_boxed_2733_, v_i_boxed_2734_, v_b_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec_ref(v_as_2725_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(lean_object* v_init_2736_, uint8_t v___x_2737_, lean_object* v_n_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
if (lean_obj_tag(v_n_2738_) == 0)
{
lean_object* v_cs_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; size_t v_sz_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v_cs_2743_ = lean_ctor_get(v_n_2738_, 0);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v_b_2739_);
v_sz_2746_ = lean_array_size(v_cs_2743_);
v___x_2747_ = ((size_t)0ULL);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2736_, v___x_2737_, v_cs_2743_, v_sz_2746_, v___x_2747_, v___x_2745_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2763_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2763_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2763_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_fst_2753_; 
v_fst_2753_ = lean_ctor_get(v_a_2749_, 0);
if (lean_obj_tag(v_fst_2753_) == 0)
{
lean_object* v_snd_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v_snd_2754_ = lean_ctor_get(v_a_2749_, 1);
lean_inc(v_snd_2754_);
lean_dec(v_a_2749_);
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_snd_2754_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2755_);
v___x_2757_ = v___x_2751_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2761_; 
lean_inc_ref(v_fst_2753_);
lean_dec(v_a_2749_);
v_val_2759_ = lean_ctor_get(v_fst_2753_, 0);
lean_inc(v_val_2759_);
lean_dec_ref_known(v_fst_2753_, 1);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v_val_2759_);
v___x_2761_ = v___x_2751_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_val_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2748_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2748_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_vs_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; size_t v_sz_2775_; size_t v___x_2776_; lean_object* v___x_2777_; 
v_vs_2772_ = lean_ctor_get(v_n_2738_, 0);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_b_2739_);
v_sz_2775_ = lean_array_size(v_vs_2772_);
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_2737_, v_vs_2772_, v_sz_2775_, v___x_2776_, v___x_2774_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2792_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2792_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2792_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v_fst_2782_; 
v_fst_2782_ = lean_ctor_get(v_a_2778_, 0);
if (lean_obj_tag(v_fst_2782_) == 0)
{
lean_object* v_snd_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v_snd_2783_ = lean_ctor_get(v_a_2778_, 1);
lean_inc(v_snd_2783_);
lean_dec(v_a_2778_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_snd_2783_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2784_);
v___x_2786_ = v___x_2780_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2790_; 
lean_inc_ref(v_fst_2782_);
lean_dec(v_a_2778_);
v_val_2788_ = lean_ctor_get(v_fst_2782_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_fst_2782_, 1);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_val_2788_);
v___x_2790_ = v___x_2780_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_val_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2777_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2777_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(lean_object* v_init_2801_, uint8_t v___x_2802_, lean_object* v_as_2803_, size_t v_sz_2804_, size_t v_i_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2805_, v_sz_2804_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_b_2806_);
return v___x_2811_;
}
else
{
lean_object* v_snd_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2846_; 
v_snd_2812_ = lean_ctor_get(v_b_2806_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_b_2806_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v_b_2806_, 0);
lean_dec(v_unused_2847_);
v___x_2814_ = v_b_2806_;
v_isShared_2815_ = v_isSharedCheck_2846_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snd_2812_);
lean_dec(v_b_2806_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2846_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_array_uget_borrowed(v_as_2803_, v_i_2805_);
lean_inc(v_snd_2812_);
v___x_2817_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2801_, v___x_2802_, v_a_2816_, v_snd_2812_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2837_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2837_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2837_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
if (lean_obj_tag(v_a_2818_) == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2818_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2822_);
v___x_2824_ = v___x_2814_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2812_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2824_);
v___x_2826_ = v___x_2820_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_del_object(v___x_2820_);
lean_dec(v_snd_2812_);
v_a_2829_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2830_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v_a_2829_);
lean_ctor_set(v___x_2814_, 0, v___x_2830_);
v___x_2832_ = v___x_2814_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_a_2829_);
v___x_2832_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
size_t v___x_2833_; size_t v___x_2834_; 
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2805_, v___x_2833_);
v_i_2805_ = v___x_2834_;
v_b_2806_ = v___x_2832_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_del_object(v___x_2814_);
lean_dec(v_snd_2812_);
v_a_2838_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2817_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2817_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(lean_object* v_init_2848_, lean_object* v___x_2849_, lean_object* v_as_2850_, lean_object* v_sz_2851_, lean_object* v_i_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v___x_13368__boxed_2857_; size_t v_sz_boxed_2858_; size_t v_i_boxed_2859_; lean_object* v_res_2860_; 
v___x_13368__boxed_2857_ = lean_unbox(v___x_2849_);
v_sz_boxed_2858_ = lean_unbox_usize(v_sz_2851_);
lean_dec(v_sz_2851_);
v_i_boxed_2859_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2848_, v___x_13368__boxed_2857_, v_as_2850_, v_sz_boxed_2858_, v_i_boxed_2859_, v_b_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_as_2850_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(lean_object* v_init_2861_, lean_object* v___x_2862_, lean_object* v_n_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v___x_13388__boxed_2868_; lean_object* v_res_2869_; 
v___x_13388__boxed_2868_ = lean_unbox(v___x_2862_);
v_res_2869_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2861_, v___x_13388__boxed_2868_, v_n_2863_, v_b_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_n_2863_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(uint8_t v___x_2870_, lean_object* v_as_2871_, size_t v_sz_2872_, size_t v_i_2873_, lean_object* v_b_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_usize_dec_lt(v_i_2873_, v_sz_2872_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_b_2874_);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v___f_2881_; lean_object* v_a_2882_; lean_object* v___x_2883_; 
lean_dec_ref(v_b_2874_);
v___x_2880_ = lean_box(v___x_2870_);
v___f_2881_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2881_, 0, v___x_2880_);
v_a_2882_ = lean_array_uget_borrowed(v_as_2871_, v_i_2873_);
lean_inc(v_a_2882_);
v___x_2883_ = l_Lean_Linter_List_binders(v_a_2882_, v___f_2881_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_n(v_a_2884_, 2);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_box(0);
v___x_2887_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2884_, v___x_2886_);
v___x_2888_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2887_, v___x_2885_, v___y_2875_, v___y_2876_);
lean_dec(v___x_2887_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref_known(v___x_2888_, 1);
lean_inc(v_a_2884_);
v___x_2889_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2884_, v___x_2886_);
v___x_2890_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2889_, v___x_2885_, v___y_2875_, v___y_2876_);
lean_dec(v___x_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec_ref_known(v___x_2890_, 1);
v___x_2891_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2884_, v___x_2886_);
v___x_2892_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2891_, v___x_2885_, v___y_2875_, v___y_2876_);
lean_dec(v___x_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; 
lean_dec_ref_known(v___x_2892_, 1);
v___x_2893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_add(v_i_2873_, v___x_2894_);
v_i_2873_ = v___x_2895_;
v_b_2874_ = v___x_2893_;
goto _start;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2892_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2892_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_a_2884_);
v_a_2905_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2890_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2890_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_a_2884_);
v_a_2913_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2888_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2888_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2933_; 
v_a_2921_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2923_ = v___x_2883_;
v_isShared_2924_ = v_isSharedCheck_2933_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2883_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2933_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_ref_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v_ref_2925_ = lean_ctor_get(v___y_2875_, 7);
v___x_2926_ = lean_io_error_to_string(v_a_2921_);
v___x_2927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = l_Lean_MessageData_ofFormat(v___x_2927_);
lean_inc(v_ref_2925_);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_ref_2925_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_2929_);
v___x_2931_ = v___x_2923_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(lean_object* v___x_2934_, lean_object* v_as_2935_, lean_object* v_sz_2936_, lean_object* v_i_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
uint8_t v___x_13572__boxed_2942_; size_t v_sz_boxed_2943_; size_t v_i_boxed_2944_; lean_object* v_res_2945_; 
v___x_13572__boxed_2942_ = lean_unbox(v___x_2934_);
v_sz_boxed_2943_ = lean_unbox_usize(v_sz_2936_);
lean_dec(v_sz_2936_);
v_i_boxed_2944_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_13572__boxed_2942_, v_as_2935_, v_sz_boxed_2943_, v_i_boxed_2944_, v_b_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v_as_2935_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(uint8_t v___x_2946_, lean_object* v_as_2947_, size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_b_2950_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v___f_2957_; lean_object* v_a_2958_; lean_object* v___x_2959_; 
lean_dec_ref(v_b_2950_);
v___x_2956_ = lean_box(v___x_2946_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2957_, 0, v___x_2956_);
v_a_2958_ = lean_array_uget_borrowed(v_as_2947_, v_i_2949_);
lean_inc(v_a_2958_);
v___x_2959_ = l_Lean_Linter_List_binders(v_a_2958_, v___f_2957_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc_n(v_a_2960_, 2);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_box(0);
v___x_2963_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2960_, v___x_2962_);
v___x_2964_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2963_, v___x_2961_, v___y_2951_, v___y_2952_);
lean_dec(v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_dec_ref_known(v___x_2964_, 1);
lean_inc(v_a_2960_);
v___x_2965_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2960_, v___x_2962_);
v___x_2966_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2965_, v___x_2961_, v___y_2951_, v___y_2952_);
lean_dec(v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_dec_ref_known(v___x_2966_, 1);
v___x_2967_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2960_, v___x_2962_);
v___x_2968_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2967_, v___x_2961_, v___y_2951_, v___y_2952_);
lean_dec(v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2949_, v___x_2970_);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_2946_, v_as_2947_, v_sz_2948_, v___x_2971_, v___x_2969_, v___y_2951_, v___y_2952_);
return v___x_2972_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
v_a_2973_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2968_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2968_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_a_2960_);
v_a_2981_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2966_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2966_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_a_2960_);
v_a_2989_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2964_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2964_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3009_; 
v_a_2997_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2999_ = v___x_2959_;
v_isShared_3000_ = v_isSharedCheck_3009_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2959_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3009_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v_ref_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v_ref_3001_ = lean_ctor_get(v___y_2951_, 7);
v___x_3002_ = lean_io_error_to_string(v_a_2997_);
v___x_3003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofFormat(v___x_3003_);
lean_inc(v_ref_3001_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_ref_3001_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3005_);
v___x_3007_ = v___x_2999_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(lean_object* v___x_3010_, lean_object* v_as_3011_, lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_b_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
uint8_t v___x_13699__boxed_3018_; size_t v_sz_boxed_3019_; size_t v_i_boxed_3020_; lean_object* v_res_3021_; 
v___x_13699__boxed_3018_ = lean_unbox(v___x_3010_);
v_sz_boxed_3019_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3020_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_13699__boxed_3018_, v_as_3011_, v_sz_boxed_3019_, v_i_boxed_3020_, v_b_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec_ref(v_as_3011_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(uint8_t v___x_3022_, lean_object* v_t_3023_, lean_object* v_init_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_root_3028_; lean_object* v_tail_3029_; lean_object* v___x_3030_; 
v_root_3028_ = lean_ctor_get(v_t_3023_, 0);
v_tail_3029_ = lean_ctor_get(v_t_3023_, 1);
v___x_3030_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_3024_, v___x_3022_, v_root_3028_, v_init_3024_, v___y_3025_, v___y_3026_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3067_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3067_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3067_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
if (lean_obj_tag(v_a_3031_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; 
v_a_3035_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v_a_3031_, 1);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_a_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; size_t v_sz_3042_; size_t v___x_3043_; lean_object* v___x_3044_; 
lean_del_object(v___x_3033_);
v_a_3039_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v_a_3031_, 1);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v_a_3039_);
v_sz_3042_ = lean_array_size(v_tail_3029_);
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_3022_, v_tail_3029_, v_sz_3042_, v___x_3043_, v___x_3041_, v___y_3025_, v___y_3026_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3058_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_fst_3049_; 
v_fst_3049_ = lean_ctor_get(v_a_3045_, 0);
if (lean_obj_tag(v_fst_3049_) == 0)
{
lean_object* v_snd_3050_; lean_object* v___x_3052_; 
v_snd_3050_ = lean_ctor_get(v_a_3045_, 1);
lean_inc(v_snd_3050_);
lean_dec(v_a_3045_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_snd_3050_);
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_snd_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v_val_3054_; lean_object* v___x_3056_; 
lean_inc_ref(v_fst_3049_);
lean_dec(v_a_3045_);
v_val_3054_ = lean_ctor_get(v_fst_3049_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v_fst_3049_, 1);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_val_3054_);
v___x_3056_ = v___x_3047_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_val_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3044_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3044_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_a_3068_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3030_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3030_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(lean_object* v___x_3076_, lean_object* v_t_3077_, lean_object* v_init_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v___x_13823__boxed_3082_; lean_object* v_res_3083_; 
v___x_13823__boxed_3082_ = lean_unbox(v___x_3076_);
v_res_3083_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v___x_13823__boxed_3082_, v_t_3077_, v_init_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v_t_3077_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0(lean_object* v_stx_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v_scopes_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_opts_3095_; lean_object* v___x_3096_; lean_object* v_name_3097_; lean_object* v_map_3098_; lean_object* v___x_3099_; 
v___x_3088_ = lean_st_ref_get(v___y_3086_);
v_scopes_3092_ = lean_ctor_get(v___x_3088_, 2);
lean_inc(v_scopes_3092_);
lean_dec(v___x_3088_);
v___x_3093_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3094_ = l_List_head_x21___redArg(v___x_3093_, v_scopes_3092_);
lean_dec(v_scopes_3092_);
v_opts_3095_ = lean_ctor_get(v___x_3094_, 1);
lean_inc_ref(v_opts_3095_);
lean_dec(v___x_3094_);
v___x_3096_ = l_Lean_Linter_List_linter_listVariables;
v_name_3097_ = lean_ctor_get(v___x_3096_, 0);
v_map_3098_ = lean_ctor_get(v_opts_3095_, 0);
lean_inc(v_map_3098_);
lean_dec_ref(v_opts_3095_);
v___x_3099_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3098_, v_name_3097_);
lean_dec(v_map_3098_);
if (lean_obj_tag(v___x_3099_) == 0)
{
goto v___jp_3089_;
}
else
{
lean_object* v_val_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3132_; 
v_val_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3132_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_val_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3132_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
if (lean_obj_tag(v_val_3100_) == 1)
{
uint8_t v_v_3104_; 
v_v_3104_ = lean_ctor_get_uint8(v_val_3100_, 0);
lean_dec_ref_known(v_val_3100_, 0);
if (v_v_3104_ == 0)
{
lean_del_object(v___x_3102_);
goto v___jp_3089_;
}
else
{
lean_object* v___x_3105_; lean_object* v_messages_3106_; uint8_t v___x_3107_; 
v___x_3105_ = lean_st_ref_get(v___y_3086_);
v_messages_3106_ = lean_ctor_get(v___x_3105_, 1);
lean_inc_ref(v_messages_3106_);
lean_dec(v___x_3105_);
v___x_3107_ = l_Lean_MessageLog_hasErrors(v_messages_3106_);
lean_dec_ref(v_messages_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v_infoState_3114_; uint8_t v_enabled_3115_; 
v___x_3108_ = lean_st_ref_get(v___y_3086_);
v_infoState_3114_ = lean_ctor_get(v___x_3108_, 8);
lean_inc_ref(v_infoState_3114_);
lean_dec(v___x_3108_);
v_enabled_3115_ = lean_ctor_get_uint8(v_infoState_3114_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3114_);
if (v_enabled_3115_ == 0)
{
goto v___jp_3109_;
}
else
{
if (v___x_3107_ == 0)
{
lean_object* v___x_3116_; lean_object* v_a_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_del_object(v___x_3102_);
v___x_3116_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_3086_);
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref(v___x_3116_);
v___x_3118_ = lean_box(0);
v___x_3119_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_enabled_3115_, v_a_3117_, v___x_3118_, v___y_3085_, v___y_3086_);
lean_dec(v_a_3117_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_3119_, 0);
lean_dec(v_unused_3127_);
v___x_3121_ = v___x_3119_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_dec(v___x_3119_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3118_);
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3118_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
return v___x_3119_;
}
}
else
{
goto v___jp_3109_;
}
}
v___jp_3109_:
{
lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3110_ = lean_box(0);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3110_);
v___x_3112_ = v___x_3102_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = lean_box(0);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3128_);
v___x_3130_ = v___x_3102_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_del_object(v___x_3102_);
lean_dec(v_val_3100_);
goto v___jp_3089_;
}
}
}
v___jp_3089_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(lean_object* v_stx_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v_stx_3133_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(lean_object* v_as_3151_, lean_object* v_as_x27_3152_, lean_object* v_b_3153_, lean_object* v_a_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_3152_, v_b_3153_, v___y_3155_, v___y_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(lean_object* v_as_3159_, lean_object* v_as_x27_3160_, lean_object* v_b_3161_, lean_object* v_a_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(v_as_3159_, v_as_x27_3160_, v_b_3161_, v_a_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v_as_x27_3160_);
lean_dec(v_as_3159_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(lean_object* v_as_3167_, lean_object* v_as_x27_3168_, lean_object* v_b_3169_, lean_object* v_a_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_3168_, v_b_3169_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(lean_object* v_as_3175_, lean_object* v_as_x27_3176_, lean_object* v_b_3177_, lean_object* v_a_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(v_as_3175_, v_as_x27_3176_, v_b_3177_, v_a_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_as_x27_3176_);
lean_dec(v_as_3175_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(lean_object* v_as_3183_, lean_object* v_as_x27_3184_, lean_object* v_b_3185_, lean_object* v_a_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_3184_, v_b_3185_, v___y_3187_, v___y_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(lean_object* v_as_3191_, lean_object* v_as_x27_3192_, lean_object* v_b_3193_, lean_object* v_a_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(v_as_3191_, v_as_x27_3192_, v_b_3193_, v_a_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v_as_x27_3192_);
lean_dec(v_as_3191_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_Linter_List_listVariablesLinter));
v___x_3201_ = l_Lean_Elab_Command_addLinter(v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
return v_res_3203_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_List_linter_indexVariables = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_List_linter_indexVariables);
lean_dec_ref(res);
res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_List_linter_listVariables = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_List_linter_listVariables);
lean_dec_ref(res);
res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_List(builtin);
}
#ifdef __cplusplus
}
#endif
