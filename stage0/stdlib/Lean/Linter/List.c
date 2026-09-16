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
uint8_t v_suppressElabErrors_boxed_842_; uint8_t v___y_10874__boxed_843_; uint8_t v_res_844_; lean_object* v_r_845_; 
v_suppressElabErrors_boxed_842_ = lean_unbox(v_suppressElabErrors_839_);
v___y_10874__boxed_843_ = lean_unbox(v___y_840_);
v_res_844_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_842_, v___y_10874__boxed_843_, v_x_841_);
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
lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; uint8_t v___y_957_; uint8_t v___y_958_; uint8_t v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; uint8_t v___y_985_; uint8_t v___y_986_; uint8_t v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; uint8_t v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; uint8_t v___x_1010_; uint8_t v___y_1012_; uint8_t v___y_1013_; uint8_t v___y_1014_; uint8_t v___y_1016_; uint8_t v___x_1028_; 
v___x_1010_ = 2;
v___x_1028_ = l_Lean_instBEqMessageSeverity_beq(v_severity_887_, v___x_1010_);
if (v___x_1028_ == 0)
{
v___y_1016_ = v___x_1028_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1029_; 
lean_inc_ref(v_msgData_886_);
v___x_1029_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_886_);
v___y_1016_ = v___x_1029_;
goto v___jp_1015_;
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
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_939_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_939_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_939_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_939_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v_currNamespace_909_; lean_object* v_openDecls_910_; lean_object* v_env_911_; lean_object* v_messages_912_; lean_object* v_scopes_913_; lean_object* v_usedQuotCtxts_914_; lean_object* v_nextMacroScope_915_; lean_object* v_maxRecDepth_916_; lean_object* v_ngen_917_; lean_object* v_auxDeclNGen_918_; lean_object* v_infoState_919_; lean_object* v_traceState_920_; lean_object* v_snapshotTasks_921_; lean_object* v_prevLinterStates_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_938_; 
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
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_938_ == 0)
{
v___x_924_ = v___x_908_;
v_isShared_925_ = v_isSharedCheck_938_;
goto v_resetjp_923_;
}
else
{
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
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_938_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_currNamespace_909_);
lean_ctor_set(v___x_926_, 1, v_openDecls_910_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___y_893_);
lean_inc_ref(v___y_895_);
lean_inc_ref(v___y_894_);
v___x_928_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_928_, 0, v___y_894_);
lean_ctor_set(v___x_928_, 1, v___y_899_);
lean_ctor_set(v___x_928_, 2, v___y_896_);
lean_ctor_set(v___x_928_, 3, v___y_895_);
lean_ctor_set(v___x_928_, 4, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5, v___y_897_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5 + 1, v___y_898_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5 + 2, v_isSilent_888_);
v___x_929_ = l_Lean_MessageLog_add(v___x_928_, v_messages_912_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_929_);
v___x_931_ = v___x_924_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_env_911_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_scopes_913_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_usedQuotCtxts_914_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_nextMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_937_, 5, v_maxRecDepth_916_);
lean_ctor_set(v_reuseFailAlloc_937_, 6, v_ngen_917_);
lean_ctor_set(v_reuseFailAlloc_937_, 7, v_auxDeclNGen_918_);
lean_ctor_set(v_reuseFailAlloc_937_, 8, v_infoState_919_);
lean_ctor_set(v_reuseFailAlloc_937_, 9, v_traceState_920_);
lean_ctor_set(v_reuseFailAlloc_937_, 10, v_snapshotTasks_921_);
lean_ctor_set(v_reuseFailAlloc_937_, 11, v_prevLinterStates_922_);
v___x_931_ = v_reuseFailAlloc_937_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_st_ref_put(v___y_900_, v___x_931_);
v___x_933_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_933_);
v___x_935_ = v___x_906_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_902_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_893_);
v_a_940_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_903_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_903_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___y_899_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_893_);
v_a_948_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_901_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_901_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_956_:
{
lean_object* v_fileName_962_; lean_object* v_fileMap_963_; uint8_t v_suppressElabErrors_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_983_; 
v_fileName_962_ = lean_ctor_get(v___y_889_, 0);
v_fileMap_963_ = lean_ctor_get(v___y_889_, 1);
v_suppressElabErrors_964_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*10);
v___x_965_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_886_);
v___x_966_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_965_, v___y_890_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_983_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_983_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_983_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref_n(v_fileMap_963_, 2);
v___x_971_ = l_Lean_FileMap_toPosition(v_fileMap_963_, v___y_960_);
lean_dec(v___y_960_);
v___x_972_ = l_Lean_FileMap_toPosition(v_fileMap_963_, v___y_961_);
lean_dec(v___y_961_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_964_ == 0)
{
lean_del_object(v___x_969_);
v___y_893_ = v_a_967_;
v___y_894_ = v_fileName_962_;
v___y_895_ = v___x_974_;
v___y_896_ = v___x_973_;
v___y_897_ = v___y_958_;
v___y_898_ = v___y_959_;
v___y_899_ = v___x_971_;
v___y_900_ = v___y_890_;
goto v___jp_892_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___f_977_; uint8_t v___x_978_; 
v___x_975_ = lean_box(v_suppressElabErrors_964_);
v___x_976_ = lean_box(v___y_957_);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_977_, 0, v___x_975_);
lean_closure_set(v___f_977_, 1, v___x_976_);
lean_inc(v_a_967_);
v___x_978_ = l_Lean_MessageData_hasTag(v___f_977_, v_a_967_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec_ref_known(v___x_973_, 1);
lean_dec_ref(v___x_971_);
lean_dec(v_a_967_);
v___x_979_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_979_);
v___x_981_ = v___x_969_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_del_object(v___x_969_);
v___y_893_ = v_a_967_;
v___y_894_ = v_fileName_962_;
v___y_895_ = v___x_974_;
v___y_896_ = v___x_973_;
v___y_897_ = v___y_958_;
v___y_898_ = v___y_959_;
v___y_899_ = v___x_971_;
v___y_900_ = v___y_890_;
goto v___jp_892_;
}
}
}
}
v___jp_984_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Syntax_getTailPos_x3f(v___y_988_, v___y_986_);
lean_dec(v___y_988_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_inc(v___y_989_);
v___y_957_ = v___y_985_;
v___y_958_ = v___y_986_;
v___y_959_ = v___y_987_;
v___y_960_ = v___y_989_;
v___y_961_ = v___y_989_;
goto v___jp_956_;
}
else
{
lean_object* v_val_991_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v___y_957_ = v___y_985_;
v___y_958_ = v___y_986_;
v___y_959_ = v___y_987_;
v___y_960_ = v___y_989_;
v___y_961_ = v_val_991_;
goto v___jp_956_;
}
}
v___jp_992_:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Elab_Command_getRef___redArg(v___y_889_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_ref_998_; lean_object* v___x_999_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v_ref_998_ = l_Lean_replaceRef(v_ref_885_, v_a_997_);
lean_dec(v_a_997_);
v___x_999_ = l_Lean_Syntax_getPos_x3f(v_ref_998_, v___y_994_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___y_985_ = v___y_993_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
v___y_988_ = v_ref_998_;
v___y_989_ = v___x_1000_;
goto v___jp_984_;
}
else
{
lean_object* v_val_1001_; 
v_val_1001_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_999_, 1);
v___y_985_ = v___y_993_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
v___y_988_ = v_ref_998_;
v___y_989_ = v_val_1001_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_msgData_886_);
v_a_1002_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_996_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
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
v___jp_1011_:
{
if (v___y_1014_ == 0)
{
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1013_;
v___y_995_ = v_severity_887_;
goto v___jp_992_;
}
else
{
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1013_;
v___y_995_ = v___x_1010_;
goto v___jp_992_;
}
}
v___jp_1015_:
{
if (v___y_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v_scopes_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_opts_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1017_ = lean_st_ref_get(v___y_890_);
v_scopes_1018_ = lean_ctor_get(v___x_1017_, 2);
lean_inc(v_scopes_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1020_ = l_List_head_x21___redArg(v___x_1019_, v_scopes_1018_);
lean_dec(v_scopes_1018_);
v_opts_1021_ = lean_ctor_get(v___x_1020_, 1);
lean_inc_ref(v_opts_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = 1;
v___x_1023_ = l_Lean_instBEqMessageSeverity_beq(v_severity_887_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_dec_ref(v_opts_1021_);
v___y_1012_ = v___y_1016_;
v___y_1013_ = v___y_1016_;
v___y_1014_ = v___x_1023_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = l_Lean_warningAsError;
v___x_1025_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_1021_, v___x_1024_);
lean_dec_ref(v_opts_1021_);
v___y_1012_ = v___y_1016_;
v___y_1013_ = v___y_1016_;
v___y_1014_ = v___x_1025_;
goto v___jp_1011_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v_msgData_886_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1030_, lean_object* v_msgData_1031_, lean_object* v_severity_1032_, lean_object* v_isSilent_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v_severity_boxed_1037_; uint8_t v_isSilent_boxed_1038_; lean_object* v_res_1039_; 
v_severity_boxed_1037_ = lean_unbox(v_severity_1032_);
v_isSilent_boxed_1038_ = lean_unbox(v_isSilent_1033_);
v_res_1039_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1030_, v_msgData_1031_, v_severity_boxed_1037_, v_isSilent_boxed_1038_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v_ref_1030_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(lean_object* v_ref_1040_, lean_object* v_msgData_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = 1;
v___x_1046_ = 0;
v___x_1047_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1040_, v_msgData_1041_, v___x_1045_, v___x_1046_, v___y_1042_, v___y_1043_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(lean_object* v_ref_1048_, lean_object* v_msgData_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_1048_, v_msgData_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v_ref_1048_);
return v_res_1053_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(lean_object* v_linterOption_1060_, lean_object* v_stx_1061_, lean_object* v_msg_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_name_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1084_; 
v_name_1066_ = lean_ctor_get(v_linterOption_1060_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_linterOption_1060_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_linterOption_1060_, 1);
lean_dec(v_unused_1085_);
v___x_1068_ = v_linterOption_1060_;
v_isShared_1069_ = v_isSharedCheck_1084_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_name_1066_);
lean_dec(v_linterOption_1060_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1084_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
lean_inc(v_name_1066_);
v___x_1071_ = l_Lean_MessageData_ofName(v_name_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 7);
lean_ctor_set(v___x_1068_, 1, v___x_1071_);
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_disable_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1074_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v_disable_1076_ = l_Lean_MessageData_note(v___x_1075_);
v___x_1077_ = l_Lean_Linter_linterMessageTag;
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_msg_1062_);
lean_ctor_set(v___x_1078_, 1, v_disable_1076_);
v___x_1079_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_name_1066_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_inc(v_stx_1061_);
v___x_1081_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_stx_1061_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_1061_, v___x_1081_, v___y_1063_, v___y_1064_);
lean_dec(v_stx_1061_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(lean_object* v_linterOption_1086_, lean_object* v_stx_1087_, lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v_linterOption_1086_, v_stx_1087_, v_msg_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(lean_object* v_a_1093_, lean_object* v_x_1094_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
uint8_t v___x_1095_; 
v___x_1095_ = 0;
return v___x_1095_;
}
else
{
lean_object* v_head_1096_; lean_object* v_tail_1097_; uint8_t v___x_1098_; 
v_head_1096_ = lean_ctor_get(v_x_1094_, 0);
v_tail_1097_ = lean_ctor_get(v_x_1094_, 1);
v___x_1098_ = lean_string_dec_eq(v_a_1093_, v_head_1096_);
if (v___x_1098_ == 0)
{
v_x_1094_ = v_tail_1097_;
goto _start;
}
else
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(lean_object* v_a_1100_, lean_object* v_x_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_1100_, v_x_1101_);
lean_dec(v_x_1101_);
lean_dec_ref(v_a_1100_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(lean_object* v_as_x27_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
if (lean_obj_tag(v_as_x27_1107_) == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_b_1108_);
return v___x_1112_;
}
else
{
lean_object* v_head_1113_; lean_object* v_tail_1114_; lean_object* v_fst_1115_; lean_object* v_snd_1116_; lean_object* v___x_1117_; 
v_head_1113_ = lean_ctor_get(v_as_x27_1107_, 0);
v_tail_1114_ = lean_ctor_get(v_as_x27_1107_, 1);
v_fst_1115_ = lean_ctor_get(v_head_1113_, 0);
v_snd_1116_ = lean_ctor_get(v_head_1113_, 1);
v___x_1117_ = lean_box(0);
if (lean_obj_tag(v_snd_1116_) == 1)
{
lean_object* v_str_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_str_1118_ = lean_ctor_get(v_snd_1116_, 1);
v___x_1119_ = ((lean_object*)(l_Lean_Linter_List_allowedWidths));
lean_inc_ref(v_str_1118_);
v___x_1120_ = l_Lean_Linter_List_stripBinderName(v_str_1118_);
v___x_1121_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1120_, v___x_1119_);
lean_dec_ref(v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1122_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1123_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
lean_inc_ref(v_str_1118_);
v___x_1124_ = l_Lean_stringToMessageData(v_str_1118_);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_inc(v_fst_1115_);
v___x_1126_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1122_, v_fst_1115_, v___x_1125_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref_known(v___x_1126_, 1);
v_as_x27_1107_ = v_tail_1114_;
v_b_1108_ = v___x_1117_;
goto _start;
}
else
{
return v___x_1126_;
}
}
else
{
v_as_x27_1107_ = v_tail_1114_;
v_b_1108_ = v___x_1117_;
goto _start;
}
}
else
{
v_as_x27_1107_ = v_tail_1114_;
v_b_1108_ = v___x_1117_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(lean_object* v_as_x27_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1130_, v_b_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_as_x27_1130_);
return v_res_1135_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(lean_object* v_as_x27_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
if (lean_obj_tag(v_as_x27_1139_) == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1140_);
return v___x_1144_;
}
else
{
lean_object* v_head_1145_; lean_object* v_tail_1146_; lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1149_; 
v_head_1145_ = lean_ctor_get(v_as_x27_1139_, 0);
v_tail_1146_ = lean_ctor_get(v_as_x27_1139_, 1);
v_fst_1147_ = lean_ctor_get(v_head_1145_, 0);
v_snd_1148_ = lean_ctor_get(v_head_1145_, 1);
v___x_1149_ = lean_box(0);
if (lean_obj_tag(v_snd_1148_) == 1)
{
lean_object* v_str_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_str_1150_ = lean_ctor_get(v_snd_1148_, 1);
v___x_1151_ = ((lean_object*)(l_Lean_Linter_List_allowedBitVecWidths));
lean_inc_ref(v_str_1150_);
v___x_1152_ = l_Lean_Linter_List_stripBinderName(v_str_1150_);
v___x_1153_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1152_, v___x_1151_);
lean_dec_ref(v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1154_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1155_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
lean_inc_ref(v_str_1150_);
v___x_1156_ = l_Lean_stringToMessageData(v_str_1150_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_inc(v_fst_1147_);
v___x_1158_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1154_, v_fst_1147_, v___x_1157_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_dec_ref_known(v___x_1158_, 1);
v_as_x27_1139_ = v_tail_1146_;
v_b_1140_ = v___x_1149_;
goto _start;
}
else
{
return v___x_1158_;
}
}
else
{
v_as_x27_1139_ = v_tail_1146_;
v_b_1140_ = v___x_1149_;
goto _start;
}
}
else
{
v_as_x27_1139_ = v_tail_1146_;
v_b_1140_ = v___x_1149_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(lean_object* v_as_x27_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1162_, v_b_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_as_x27_1162_);
return v_res_1167_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(lean_object* v_as_x27_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
if (lean_obj_tag(v_as_x27_1171_) == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_b_1172_);
return v___x_1176_;
}
else
{
lean_object* v_head_1177_; lean_object* v_tail_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; 
v_head_1177_ = lean_ctor_get(v_as_x27_1171_, 0);
v_tail_1178_ = lean_ctor_get(v_as_x27_1171_, 1);
v_fst_1179_ = lean_ctor_get(v_head_1177_, 0);
v_snd_1180_ = lean_ctor_get(v_head_1177_, 1);
v___x_1181_ = lean_box(0);
if (lean_obj_tag(v_snd_1180_) == 1)
{
lean_object* v_str_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_str_1182_ = lean_ctor_get(v_snd_1180_, 1);
v___x_1183_ = ((lean_object*)(l_Lean_Linter_List_allowedIndices));
lean_inc_ref(v_str_1182_);
v___x_1184_ = l_Lean_Linter_List_stripBinderName(v_str_1182_);
v___x_1185_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1184_, v___x_1183_);
lean_dec_ref(v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1187_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
lean_inc_ref(v_str_1182_);
v___x_1188_ = l_Lean_stringToMessageData(v_str_1182_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
lean_inc(v_fst_1179_);
v___x_1190_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1186_, v_fst_1179_, v___x_1189_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_dec_ref_known(v___x_1190_, 1);
v_as_x27_1171_ = v_tail_1178_;
v_b_1172_ = v___x_1181_;
goto _start;
}
else
{
return v___x_1190_;
}
}
else
{
v_as_x27_1171_ = v_tail_1178_;
v_b_1172_ = v___x_1181_;
goto _start;
}
}
else
{
v_as_x27_1171_ = v_tail_1178_;
v_b_1172_ = v___x_1181_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(lean_object* v_as_x27_1194_, lean_object* v_b_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1194_, v_b_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v_as_x27_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(lean_object* v_as_1203_, size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_b_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_b_1206_);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v_b_1206_);
v___x_1212_ = lean_box(0);
v_a_1213_ = lean_array_uget_borrowed(v_as_1203_, v_i_1205_);
lean_inc(v_a_1213_);
v___x_1214_ = l_Lean_Linter_List_numericalIndices(v_a_1213_);
v___x_1215_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1214_, v___x_1212_, v___y_1207_, v___y_1208_);
lean_dec(v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref_known(v___x_1215_, 1);
lean_inc(v_a_1213_);
v___x_1216_ = l_Lean_Linter_List_numericalWidths(v_a_1213_);
v___x_1217_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1216_, v___x_1212_, v___y_1207_, v___y_1208_);
lean_dec(v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref_known(v___x_1217_, 1);
lean_inc(v_a_1213_);
v___x_1218_ = l_Lean_Linter_List_bitVecWidths(v_a_1213_);
v___x_1219_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1218_, v___x_1212_, v___y_1207_, v___y_1208_);
lean_dec(v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; 
lean_dec_ref_known(v___x_1219_, 1);
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1205_, v___x_1221_);
v_i_1205_ = v___x_1222_;
v_b_1206_ = v___x_1220_;
goto _start;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
v_a_1224_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1219_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1219_);
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
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1217_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1217_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1215_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1215_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(lean_object* v_as_1248_, lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
size_t v_sz_boxed_1255_; size_t v_i_boxed_1256_; lean_object* v_res_1257_; 
v_sz_boxed_1255_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1248_, v_sz_boxed_1255_, v_i_boxed_1256_, v_b_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_as_1248_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(lean_object* v_as_1258_, size_t v_sz_1259_, size_t v_i_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_usize_dec_lt(v_i_1260_, v_sz_1259_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_b_1261_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_b_1261_);
v___x_1267_ = lean_box(0);
v_a_1268_ = lean_array_uget_borrowed(v_as_1258_, v_i_1260_);
lean_inc(v_a_1268_);
v___x_1269_ = l_Lean_Linter_List_numericalIndices(v_a_1268_);
v___x_1270_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1269_, v___x_1267_, v___y_1262_, v___y_1263_);
lean_dec(v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref_known(v___x_1270_, 1);
lean_inc(v_a_1268_);
v___x_1271_ = l_Lean_Linter_List_numericalWidths(v_a_1268_);
v___x_1272_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1271_, v___x_1267_, v___y_1262_, v___y_1263_);
lean_dec(v___x_1271_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref_known(v___x_1272_, 1);
lean_inc(v_a_1268_);
v___x_1273_ = l_Lean_Linter_List_bitVecWidths(v_a_1268_);
v___x_1274_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1273_, v___x_1267_, v___y_1262_, v___y_1263_);
lean_dec(v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref_known(v___x_1274_, 1);
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1260_, v___x_1276_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1258_, v_sz_1259_, v___x_1277_, v___x_1275_, v___y_1262_, v___y_1263_);
return v___x_1278_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1274_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1274_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1272_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1272_);
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
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1270_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1270_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_1303_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v_as_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(lean_object* v_init_1313_, lean_object* v_n_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
if (lean_obj_tag(v_n_1314_) == 0)
{
lean_object* v_cs_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v_cs_1319_ = lean_ctor_get(v_n_1314_, 0);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v_b_1315_);
v_sz_1322_ = lean_array_size(v_cs_1319_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1313_, v_cs_1319_, v_sz_1322_, v___x_1323_, v___x_1321_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1339_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_fst_1329_; 
v_fst_1329_ = lean_ctor_get(v_a_1325_, 0);
if (lean_obj_tag(v_fst_1329_) == 0)
{
lean_object* v_snd_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_snd_1330_ = lean_ctor_get(v_a_1325_, 1);
lean_inc(v_snd_1330_);
lean_dec(v_a_1325_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_snd_1330_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1331_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1337_; 
lean_inc_ref(v_fst_1329_);
lean_dec(v_a_1325_);
v_val_1335_ = lean_ctor_get(v_fst_1329_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_fst_1329_, 1);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_val_1335_);
v___x_1337_ = v___x_1327_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1324_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1324_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_vs_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; size_t v_sz_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v_vs_1348_ = lean_ctor_get(v_n_1314_, 0);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_b_1315_);
v_sz_1351_ = lean_array_size(v_vs_1348_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_1348_, v_sz_1351_, v___x_1352_, v___x_1350_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1368_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; 
v_fst_1358_ = lean_ctor_get(v_a_1354_, 0);
if (lean_obj_tag(v_fst_1358_) == 0)
{
lean_object* v_snd_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v_snd_1359_ = lean_ctor_get(v_a_1354_, 1);
lean_inc(v_snd_1359_);
lean_dec(v_a_1354_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_snd_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v_val_1364_; lean_object* v___x_1366_; 
lean_inc_ref(v_fst_1358_);
lean_dec(v_a_1354_);
v_val_1364_ = lean_ctor_get(v_fst_1358_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v_fst_1358_, 1);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_val_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_val_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1353_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1353_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(lean_object* v_init_1377_, lean_object* v_as_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_b_1381_);
return v___x_1386_;
}
else
{
lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1421_; 
v_snd_1387_ = lean_ctor_get(v_b_1381_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_b_1381_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_b_1381_, 0);
lean_dec(v_unused_1422_);
v___x_1389_ = v_b_1381_;
v_isShared_1390_ = v_isSharedCheck_1421_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_dec(v_b_1381_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1421_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_a_1391_; lean_object* v___x_1392_; 
v_a_1391_ = lean_array_uget_borrowed(v_as_1378_, v_i_1380_);
lean_inc(v_snd_1387_);
v___x_1392_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1377_, v_a_1391_, v_snd_1387_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1412_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1412_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1412_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
if (lean_obj_tag(v_a_1393_) == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1393_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1397_);
v___x_1399_ = v___x_1389_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1387_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1401_ = v___x_1395_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_del_object(v___x_1395_);
lean_dec(v_snd_1387_);
v_a_1404_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v_a_1393_, 1);
v___x_1405_ = lean_box(0);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_a_1404_);
lean_ctor_set(v___x_1389_, 0, v___x_1405_);
v___x_1407_ = v___x_1389_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_a_1404_);
v___x_1407_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
size_t v___x_1408_; size_t v___x_1409_; 
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1380_, v___x_1408_);
v_i_1380_ = v___x_1409_;
v_b_1381_ = v___x_1407_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
v_a_1413_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1392_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1392_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(lean_object* v_init_1423_, lean_object* v_as_1424_, lean_object* v_sz_1425_, lean_object* v_i_1426_, lean_object* v_b_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; lean_object* v_res_1433_; 
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1425_);
lean_dec(v_sz_1425_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1423_, v_as_1424_, v_sz_boxed_1431_, v_i_boxed_1432_, v_b_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_as_1424_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(lean_object* v_init_1434_, lean_object* v_n_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1434_, v_n_1435_, v_b_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_n_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(lean_object* v_as_1444_, size_t v_sz_1445_, size_t v_i_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_lt(v_i_1446_, v_sz_1445_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_b_1447_);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec_ref(v_b_1447_);
v___x_1453_ = lean_box(0);
v_a_1454_ = lean_array_uget_borrowed(v_as_1444_, v_i_1446_);
lean_inc(v_a_1454_);
v___x_1455_ = l_Lean_Linter_List_numericalIndices(v_a_1454_);
v___x_1456_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1455_, v___x_1453_, v___y_1448_, v___y_1449_);
lean_dec(v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref_known(v___x_1456_, 1);
lean_inc(v_a_1454_);
v___x_1457_ = l_Lean_Linter_List_numericalWidths(v_a_1454_);
v___x_1458_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1457_, v___x_1453_, v___y_1448_, v___y_1449_);
lean_dec(v___x_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref_known(v___x_1458_, 1);
lean_inc(v_a_1454_);
v___x_1459_ = l_Lean_Linter_List_bitVecWidths(v_a_1454_);
v___x_1460_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1459_, v___x_1453_, v___y_1448_, v___y_1449_);
lean_dec(v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; 
lean_dec_ref_known(v___x_1460_, 1);
v___x_1461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1462_ = ((size_t)1ULL);
v___x_1463_ = lean_usize_add(v_i_1446_, v___x_1462_);
v_i_1446_ = v___x_1463_;
v_b_1447_ = v___x_1461_;
goto _start;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1460_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1460_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1458_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1458_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1456_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1456_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(lean_object* v_as_1489_, lean_object* v_sz_1490_, lean_object* v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1490_);
lean_dec(v_sz_1490_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1489_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v_as_1489_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_b_1502_);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_b_1502_);
v___x_1508_ = lean_box(0);
v_a_1509_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
lean_inc(v_a_1509_);
v___x_1510_ = l_Lean_Linter_List_numericalIndices(v_a_1509_);
v___x_1511_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1510_, v___x_1508_, v___y_1503_, v___y_1504_);
lean_dec(v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1511_, 1);
lean_inc(v_a_1509_);
v___x_1512_ = l_Lean_Linter_List_numericalWidths(v_a_1509_);
v___x_1513_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1512_, v___x_1508_, v___y_1503_, v___y_1504_);
lean_dec(v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref_known(v___x_1513_, 1);
lean_inc(v_a_1509_);
v___x_1514_ = l_Lean_Linter_List_bitVecWidths(v_a_1509_);
v___x_1515_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1514_, v___x_1508_, v___y_1503_, v___y_1504_);
lean_dec(v___x_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref_known(v___x_1515_, 1);
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1501_, v___x_1517_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1499_, v_sz_1500_, v___x_1518_, v___x_1516_, v___y_1503_, v___y_1504_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1515_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1515_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1513_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1513_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1511_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1511_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(lean_object* v_as_1544_, lean_object* v_sz_1545_, lean_object* v_i_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_sz_boxed_1551_; size_t v_i_boxed_1552_; lean_object* v_res_1553_; 
v_sz_boxed_1551_ = lean_unbox_usize(v_sz_1545_);
lean_dec(v_sz_1545_);
v_i_boxed_1552_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_1544_, v_sz_boxed_1551_, v_i_boxed_1552_, v_b_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v_as_1544_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(lean_object* v_t_1554_, lean_object* v_init_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_root_1559_; lean_object* v_tail_1560_; lean_object* v___x_1561_; 
v_root_1559_ = lean_ctor_get(v_t_1554_, 0);
v_tail_1560_ = lean_ctor_get(v_t_1554_, 1);
v___x_1561_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1555_, v_root_1559_, v_init_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1598_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1598_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1598_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
if (lean_obj_tag(v_a_1562_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v_a_1562_, 1);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v_a_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1564_);
v_a_1570_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v_a_1562_, 1);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1570_);
v_sz_1573_ = lean_array_size(v_tail_1560_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_1560_, v_sz_1573_, v___x_1574_, v___x_1572_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1589_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_fst_1580_; 
v_fst_1580_ = lean_ctor_get(v_a_1576_, 0);
if (lean_obj_tag(v_fst_1580_) == 0)
{
lean_object* v_snd_1581_; lean_object* v___x_1583_; 
v_snd_1581_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_snd_1581_);
lean_dec(v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_snd_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_snd_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1587_; 
lean_inc_ref(v_fst_1580_);
lean_dec(v_a_1576_);
v_val_1585_ = lean_ctor_get(v_fst_1580_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_fst_1580_, 1);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_val_1585_);
v___x_1587_ = v___x_1578_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_val_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1575_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1575_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1561_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1561_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(lean_object* v_t_1607_, lean_object* v_init_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_t_1607_, v_init_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_t_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0(lean_object* v_stx_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v_scopes_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_opts_1624_; lean_object* v___x_1625_; lean_object* v_name_1626_; lean_object* v_map_1627_; lean_object* v___x_1628_; 
v___x_1617_ = lean_st_ref_get(v___y_1615_);
v_scopes_1621_ = lean_ctor_get(v___x_1617_, 2);
lean_inc(v_scopes_1621_);
lean_dec(v___x_1617_);
v___x_1622_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1623_ = l_List_head_x21___redArg(v___x_1622_, v_scopes_1621_);
lean_dec(v_scopes_1621_);
v_opts_1624_ = lean_ctor_get(v___x_1623_, 1);
lean_inc_ref(v_opts_1624_);
lean_dec(v___x_1623_);
v___x_1625_ = l_Lean_Linter_List_linter_indexVariables;
v_name_1626_ = lean_ctor_get(v___x_1625_, 0);
v_map_1627_ = lean_ctor_get(v_opts_1624_, 0);
lean_inc(v_map_1627_);
lean_dec_ref(v_opts_1624_);
v___x_1628_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1627_, v_name_1626_);
lean_dec(v_map_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
goto v___jp_1618_;
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1661_; 
v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1661_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_val_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1661_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_val_1629_) == 1)
{
uint8_t v_v_1633_; 
v_v_1633_ = lean_ctor_get_uint8(v_val_1629_, 0);
lean_dec_ref_known(v_val_1629_, 0);
if (v_v_1633_ == 0)
{
lean_del_object(v___x_1631_);
goto v___jp_1618_;
}
else
{
lean_object* v___x_1634_; lean_object* v_messages_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_st_ref_get(v___y_1615_);
v_messages_1635_ = lean_ctor_get(v___x_1634_, 1);
lean_inc_ref(v_messages_1635_);
lean_dec(v___x_1634_);
v___x_1636_ = l_Lean_MessageLog_hasErrors(v_messages_1635_);
lean_dec_ref(v_messages_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v_infoState_1643_; uint8_t v_enabled_1644_; 
v___x_1637_ = lean_st_ref_get(v___y_1615_);
v_infoState_1643_ = lean_ctor_get(v___x_1637_, 8);
lean_inc_ref(v_infoState_1643_);
lean_dec(v___x_1637_);
v_enabled_1644_ = lean_ctor_get_uint8(v_infoState_1643_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1643_);
if (v_enabled_1644_ == 0)
{
goto v___jp_1638_;
}
else
{
if (v___x_1636_ == 0)
{
lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_del_object(v___x_1631_);
v___x_1645_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_1615_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_1646_, v___x_1647_, v___y_1614_, v___y_1615_);
lean_dec(v_a_1646_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1648_, 0);
lean_dec(v_unused_1656_);
v___x_1650_ = v___x_1648_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v___x_1648_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1647_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1647_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
return v___x_1648_;
}
}
else
{
goto v___jp_1638_;
}
}
v___jp_1638_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1639_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1657_);
v___x_1659_ = v___x_1631_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_del_object(v___x_1631_);
lean_dec(v_val_1629_);
goto v___jp_1618_;
}
}
}
v___jp_1618_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0___boxed(lean_object* v_stx_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v_stx_1662_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(lean_object* v_as_1680_, lean_object* v_as_x27_1681_, lean_object* v_b_1682_, lean_object* v_a_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1681_, v_b_1682_, v___y_1684_, v___y_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(lean_object* v_as_1688_, lean_object* v_as_x27_1689_, lean_object* v_b_1690_, lean_object* v_a_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(v_as_1688_, v_as_x27_1689_, v_b_1690_, v_a_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_as_x27_1689_);
lean_dec(v_as_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(lean_object* v_as_1696_, lean_object* v_as_x27_1697_, lean_object* v_b_1698_, lean_object* v_a_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1697_, v_b_1698_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(lean_object* v_as_1704_, lean_object* v_as_x27_1705_, lean_object* v_b_1706_, lean_object* v_a_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(v_as_1704_, v_as_x27_1705_, v_b_1706_, v_a_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_as_x27_1705_);
lean_dec(v_as_1704_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(lean_object* v_as_1712_, lean_object* v_as_x27_1713_, lean_object* v_b_1714_, lean_object* v_a_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1713_, v_b_1714_, v___y_1716_, v___y_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(lean_object* v_as_1720_, lean_object* v_as_x27_1721_, lean_object* v_b_1722_, lean_object* v_a_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(v_as_1720_, v_as_x27_1721_, v_b_1722_, v_a_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v_as_x27_1721_);
lean_dec(v_as_1720_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(lean_object* v_msgData_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_1728_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_msgData_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_Linter_List_indexLinter));
v___x_1740_ = l_Lean_Elab_Command_addLinter(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(lean_object* v_e_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_Expr_hasMVar(v_e_1801_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_e_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v_mctx_1807_; lean_object* v___x_1808_; lean_object* v_fst_1809_; lean_object* v_snd_1810_; lean_object* v___x_1811_; lean_object* v_cache_1812_; lean_object* v_zetaDeltaFVarIds_1813_; lean_object* v_postponed_1814_; lean_object* v_diag_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
v___x_1806_ = lean_st_ref_get(v___y_1802_);
v_mctx_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_ref(v_mctx_1807_);
lean_dec(v___x_1806_);
v___x_1808_ = l_Lean_instantiateMVarsCore(v_mctx_1807_, v_e_1801_);
v_fst_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_fst_1809_);
v_snd_1810_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_snd_1810_);
lean_dec_ref(v___x_1808_);
v___x_1811_ = lean_st_ref_take(v___y_1802_);
v_cache_1812_ = lean_ctor_get(v___x_1811_, 1);
v_zetaDeltaFVarIds_1813_ = lean_ctor_get(v___x_1811_, 2);
v_postponed_1814_ = lean_ctor_get(v___x_1811_, 3);
v_diag_1815_ = lean_ctor_get(v___x_1811_, 4);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1825_);
v___x_1817_ = v___x_1811_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_diag_1815_);
lean_inc(v_postponed_1814_);
lean_inc(v_zetaDeltaFVarIds_1813_);
lean_inc(v_cache_1812_);
lean_dec(v___x_1811_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v_snd_1810_);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_snd_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_cache_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_zetaDeltaFVarIds_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_postponed_1814_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_diag_1815_);
v___x_1820_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_st_ref_put(v___y_1802_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_fst_1809_);
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(lean_object* v_e_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1826_, v___y_1827_);
lean_dec(v___y_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(lean_object* v_e_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1830_, v___y_1832_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(lean_object* v_e_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(v_e_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1843_;
}
}
static lean_object* _init_l_Lean_Linter_List_binders___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
v___x_1848_ = ((lean_object*)(l_Lean_Linter_List_binders___lam__0___closed__1));
v___x_1849_ = l_Lean_Expr_const___override(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0(lean_object* v_expr_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___y_1857_; lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_saveState___redArg(v___y_1852_, v___y_1854_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
lean_inc(v___y_1854_);
lean_inc(v___y_1852_);
v___x_1862_ = lean_infer_type(v_expr_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec(v_a_1861_);
lean_dec(v___y_1854_);
v___y_1857_ = v___x_1862_;
goto v___jp_1856_;
}
else
{
lean_object* v_a_1863_; uint8_t v___y_1865_; uint8_t v___x_1877_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
v___x_1877_ = l_Lean_Exception_isInterrupt(v_a_1863_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; 
v___x_1878_ = l_Lean_Exception_isRuntime(v_a_1863_);
v___y_1865_ = v___x_1878_;
goto v___jp_1864_;
}
else
{
lean_dec(v_a_1863_);
v___y_1865_ = v___x_1877_;
goto v___jp_1864_;
}
v___jp_1864_:
{
if (v___y_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref_known(v___x_1862_, 1);
v___x_1866_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1861_, v___y_1852_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec(v_a_1861_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref_known(v___x_1866_, 1);
v___x_1867_ = lean_obj_once(&l_Lean_Linter_List_binders___lam__0___closed__2, &l_Lean_Linter_List_binders___lam__0___closed__2_once, _init_l_Lean_Linter_List_binders___lam__0___closed__2);
v___x_1868_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_1867_, v___y_1852_);
lean_dec(v___y_1852_);
return v___x_1868_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v___y_1852_);
v_a_1869_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1866_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1866_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_dec(v_a_1861_);
lean_dec(v___y_1854_);
v___y_1857_ = v___x_1862_;
goto v___jp_1856_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_expr_1850_);
v_a_1879_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1860_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1860_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
v___jp_1856_:
{
if (lean_obj_tag(v___y_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___y_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___y_1857_, 1);
v___x_1859_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_a_1858_, v___y_1852_);
lean_dec(v___y_1852_);
return v___x_1859_;
}
else
{
lean_dec(v___y_1852_);
return v___y_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0___boxed(lean_object* v_expr_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Linter_List_binders___lam__0(v_expr_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1(lean_object* v_p_1894_, lean_object* v_ctx_1895_, lean_object* v_ti_1896_){
_start:
{
uint8_t v_isBinder_1898_; 
v_isBinder_1898_ = lean_ctor_get_uint8(v_ti_1896_, sizeof(void*)*4);
if (v_isBinder_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec_ref(v_ti_1896_);
lean_dec_ref(v_ctx_1895_);
lean_dec_ref(v_p_1894_);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v_toElabInfo_1901_; lean_object* v_lctx_1902_; lean_object* v_expr_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; 
v_toElabInfo_1901_ = lean_ctor_get(v_ti_1896_, 0);
lean_inc_ref(v_toElabInfo_1901_);
v_lctx_1902_ = lean_ctor_get(v_ti_1896_, 1);
lean_inc_ref_n(v_lctx_1902_, 2);
v_expr_1903_ = lean_ctor_get(v_ti_1896_, 3);
lean_inc_ref_n(v_expr_1903_, 2);
lean_dec_ref(v_ti_1896_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1904_, 0, v_expr_1903_);
v___x_1905_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1895_, v_lctx_1902_, v___f_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1949_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1949_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1949_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
lean_inc(v_a_1906_);
v___x_1910_ = l_Lean_Expr_cleanupAnnotations(v_a_1906_);
v___x_1911_ = lean_apply_1(v_p_1894_, v___x_1910_);
v___x_1912_ = lean_unbox(v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_a_1906_);
lean_dec_ref(v_expr_1903_);
lean_dec_ref(v_lctx_1902_);
lean_dec_ref(v_toElabInfo_1901_);
v___x_1913_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1913_);
v___x_1915_ = v___x_1908_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
if (lean_obj_tag(v_expr_1903_) == 1)
{
lean_object* v_fvarId_1917_; lean_object* v___x_1918_; 
v_fvarId_1917_ = lean_ctor_get(v_expr_1903_, 0);
lean_inc(v_fvarId_1917_);
lean_dec_ref_known(v_expr_1903_, 1);
v___x_1918_ = lean_local_ctx_find(v_lctx_1902_, v_fvarId_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_dec(v_a_1906_);
lean_dec_ref(v_toElabInfo_1901_);
v___x_1919_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1919_);
v___x_1921_ = v___x_1908_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
else
{
lean_object* v_val_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1944_; 
v_val_1923_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1925_ = v___x_1918_;
v_isShared_1926_ = v_isSharedCheck_1944_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_val_1923_);
lean_dec(v___x_1918_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1944_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_stx_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1942_; 
v_stx_1927_ = lean_ctor_get(v_toElabInfo_1901_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_toElabInfo_1901_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_toElabInfo_1901_, 0);
lean_dec(v_unused_1943_);
v___x_1929_ = v_toElabInfo_1901_;
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_stx_1927_);
lean_dec(v_toElabInfo_1901_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = l_Lean_LocalDecl_userName(v_val_1923_);
lean_dec(v_val_1923_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v_a_1906_);
lean_ctor_set(v___x_1929_, 0, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_a_1906_);
v___x_1933_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_stx_1927_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1934_);
v___x_1936_ = v___x_1925_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1936_);
v___x_1938_ = v___x_1908_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec(v_a_1906_);
lean_dec_ref(v_expr_1903_);
lean_dec_ref(v_lctx_1902_);
lean_dec_ref(v_toElabInfo_1901_);
v___x_1945_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1945_);
v___x_1947_ = v___x_1908_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_expr_1903_);
lean_dec_ref(v_lctx_1902_);
lean_dec_ref(v_toElabInfo_1901_);
lean_dec_ref(v_p_1894_);
v_a_1950_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1905_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1905_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1___boxed(lean_object* v_p_1958_, lean_object* v_ctx_1959_, lean_object* v_ti_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Linter_List_binders___lam__1(v_p_1958_, v_ctx_1959_, v_ti_1960_);
return v_res_1962_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1964_, lean_object* v___x_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_object* v_cs_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1982_; 
v_cs_1969_ = lean_ctor_get(v_x_1966_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_x_1966_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1971_ = v_x_1966_;
v_isShared_1972_ = v_isSharedCheck_1982_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_cs_1969_);
lean_dec(v_x_1966_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1982_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_cs_1969_);
v___x_1975_ = lean_nat_dec_lt(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref(v_cs_1969_);
lean_dec(v___x_1965_);
lean_dec_ref(v_f_1964_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_x_1967_);
v___x_1977_ = v___x_1971_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_x_1967_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1971_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1974_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_1964_, v___x_1965_, v_cs_1969_, v___x_1979_, v___x_1980_, v_x_1967_);
lean_dec_ref(v_cs_1969_);
return v___x_1981_;
}
}
}
else
{
lean_object* v_vs_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1996_; 
v_vs_1983_ = lean_ctor_get(v_x_1966_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_x_1966_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1985_ = v_x_1966_;
v_isShared_1986_ = v_isSharedCheck_1996_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_vs_1983_);
lean_dec(v_x_1966_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1996_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_size(v_vs_1983_);
v___x_1989_ = lean_nat_dec_lt(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v_vs_1983_);
lean_dec(v___x_1965_);
lean_dec_ref(v_f_1964_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 0);
lean_ctor_set(v___x_1985_, 0, v_x_1967_);
v___x_1991_ = v___x_1985_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_x_1967_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
else
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
lean_del_object(v___x_1985_);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = lean_usize_of_nat(v___x_1988_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1964_, v___x_1965_, v_vs_1983_, v___x_1993_, v___x_1994_, v_x_1967_);
lean_dec_ref(v_vs_1983_);
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_f_1997_, lean_object* v___x_1998_, lean_object* v_as_1999_, size_t v_i_2000_, size_t v_stop_2001_, lean_object* v_b_2002_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_eq(v_i_2000_, v_stop_2001_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_array_uget_borrowed(v_as_1999_, v_i_2000_);
lean_inc(v___x_2005_);
lean_inc(v___x_1998_);
lean_inc_ref(v_f_1997_);
v___x_2006_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1997_, v___x_1998_, v___x_2005_, v_b_2002_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; size_t v___x_2008_; size_t v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_2000_, v___x_2008_);
v_i_2000_ = v___x_2009_;
v_b_2002_ = v_a_2007_;
goto _start;
}
else
{
lean_dec(v___x_1998_);
lean_dec_ref(v_f_1997_);
return v___x_2006_;
}
}
else
{
lean_object* v___x_2011_; 
lean_dec(v___x_1998_);
lean_dec_ref(v_f_1997_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_b_2002_);
return v___x_2011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_f_2012_, lean_object* v___x_2013_, lean_object* v_x_2014_, size_t v_x_2015_, size_t v_x_2016_, lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2014_) == 0)
{
lean_object* v_cs_2019_; lean_object* v___x_2020_; size_t v___x_2021_; lean_object* v_j_2022_; lean_object* v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; 
v_cs_2019_ = lean_ctor_get(v_x_2014_, 0);
lean_inc_ref(v_cs_2019_);
lean_dec_ref_known(v_x_2014_, 1);
v___x_2020_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2021_ = lean_usize_shift_right(v_x_2015_, v_x_2016_);
v_j_2022_ = lean_usize_to_nat(v___x_2021_);
v___x_2023_ = lean_array_get_borrowed(v___x_2020_, v_cs_2019_, v_j_2022_);
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_shift_left(v___x_2024_, v_x_2016_);
v___x_2026_ = lean_usize_sub(v___x_2025_, v___x_2024_);
v___x_2027_ = lean_usize_land(v_x_2015_, v___x_2026_);
v___x_2028_ = ((size_t)5ULL);
v___x_2029_ = lean_usize_sub(v_x_2016_, v___x_2028_);
lean_inc(v___x_2023_);
lean_inc(v___x_2013_);
lean_inc_ref(v_f_2012_);
v___x_2030_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2012_, v___x_2013_, v___x_2023_, v___x_2027_, v___x_2029_, v_x_2017_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_j_2022_, v___x_2032_);
lean_dec(v_j_2022_);
v___x_2034_ = lean_array_get_size(v_cs_2019_);
v___x_2035_ = lean_nat_dec_lt(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_dec(v___x_2033_);
lean_dec(v_a_2031_);
lean_dec_ref(v_cs_2019_);
lean_dec(v___x_2013_);
lean_dec_ref(v_f_2012_);
return v___x_2030_;
}
else
{
size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref_known(v___x_2030_, 1);
v___x_2036_ = lean_usize_of_nat(v___x_2033_);
lean_dec(v___x_2033_);
v___x_2037_ = lean_usize_of_nat(v___x_2034_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2012_, v___x_2013_, v_cs_2019_, v___x_2036_, v___x_2037_, v_a_2031_);
lean_dec_ref(v_cs_2019_);
return v___x_2038_;
}
}
else
{
lean_dec(v_j_2022_);
lean_dec_ref(v_cs_2019_);
lean_dec(v___x_2013_);
lean_dec_ref(v_f_2012_);
return v___x_2030_;
}
}
else
{
lean_object* v_vs_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2052_; 
v_vs_2039_ = lean_ctor_get(v_x_2014_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_x_2014_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2041_ = v_x_2014_;
v_isShared_2042_ = v_isSharedCheck_2052_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_vs_2039_);
lean_dec(v_x_2014_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2052_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2043_ = lean_usize_to_nat(v_x_2015_);
v___x_2044_ = lean_array_get_size(v_vs_2039_);
v___x_2045_ = lean_nat_dec_lt(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2047_; 
lean_dec(v___x_2043_);
lean_dec_ref(v_vs_2039_);
lean_dec(v___x_2013_);
lean_dec_ref(v_f_2012_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 0);
lean_ctor_set(v___x_2041_, 0, v_x_2017_);
v___x_2047_ = v___x_2041_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_x_2017_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
lean_del_object(v___x_2041_);
v___x_2049_ = lean_usize_of_nat(v___x_2043_);
lean_dec(v___x_2043_);
v___x_2050_ = lean_usize_of_nat(v___x_2044_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2012_, v___x_2013_, v_vs_2039_, v___x_2049_, v___x_2050_, v_x_2017_);
lean_dec_ref(v_vs_2039_);
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_2053_, lean_object* v___x_2054_, lean_object* v_t_2055_, lean_object* v_init_2056_, lean_object* v_start_2057_){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = lean_nat_dec_eq(v_start_2057_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v_root_2061_; lean_object* v_tail_2062_; size_t v_shift_2063_; lean_object* v_tailOff_2064_; uint8_t v___x_2065_; 
v_root_2061_ = lean_ctor_get(v_t_2055_, 0);
lean_inc_ref(v_root_2061_);
v_tail_2062_ = lean_ctor_get(v_t_2055_, 1);
lean_inc_ref(v_tail_2062_);
v_shift_2063_ = lean_ctor_get_usize(v_t_2055_, 4);
v_tailOff_2064_ = lean_ctor_get(v_t_2055_, 3);
lean_inc(v_tailOff_2064_);
lean_dec_ref(v_t_2055_);
v___x_2065_ = lean_nat_dec_le(v_tailOff_2064_, v_start_2057_);
if (v___x_2065_ == 0)
{
size_t v___x_2066_; lean_object* v___x_2067_; 
lean_dec(v_tailOff_2064_);
v___x_2066_ = lean_usize_of_nat(v_start_2057_);
lean_inc(v___x_2054_);
lean_inc_ref(v_f_2053_);
v___x_2067_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2053_, v___x_2054_, v_root_2061_, v___x_2066_, v_shift_2063_, v_init_2056_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
v___x_2069_ = lean_array_get_size(v_tail_2062_);
v___x_2070_ = lean_nat_dec_lt(v___x_2059_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_dec(v_a_2068_);
lean_dec_ref(v_tail_2062_);
lean_dec(v___x_2054_);
lean_dec_ref(v_f_2053_);
return v___x_2067_;
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref_known(v___x_2067_, 1);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2069_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2053_, v___x_2054_, v_tail_2062_, v___x_2071_, v___x_2072_, v_a_2068_);
lean_dec_ref(v_tail_2062_);
return v___x_2073_;
}
}
else
{
lean_dec_ref(v_tail_2062_);
lean_dec(v___x_2054_);
lean_dec_ref(v_f_2053_);
return v___x_2067_;
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_dec_ref(v_root_2061_);
v___x_2074_ = lean_nat_sub(v_start_2057_, v_tailOff_2064_);
lean_dec(v_tailOff_2064_);
v___x_2075_ = lean_array_get_size(v_tail_2062_);
v___x_2076_ = lean_nat_dec_lt(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v___x_2074_);
lean_dec_ref(v_tail_2062_);
lean_dec(v___x_2054_);
lean_dec_ref(v_f_2053_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_init_2056_);
return v___x_2077_;
}
else
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_usize_of_nat(v___x_2074_);
lean_dec(v___x_2074_);
v___x_2079_ = lean_usize_of_nat(v___x_2075_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2053_, v___x_2054_, v_tail_2062_, v___x_2078_, v___x_2079_, v_init_2056_);
lean_dec_ref(v_tail_2062_);
return v___x_2080_;
}
}
}
else
{
lean_object* v_root_2081_; lean_object* v_tail_2082_; lean_object* v___x_2083_; 
v_root_2081_ = lean_ctor_get(v_t_2055_, 0);
lean_inc_ref(v_root_2081_);
v_tail_2082_ = lean_ctor_get(v_t_2055_, 1);
lean_inc_ref(v_tail_2082_);
lean_dec_ref(v_t_2055_);
lean_inc(v___x_2054_);
lean_inc_ref(v_f_2053_);
v___x_2083_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2053_, v___x_2054_, v_root_2081_, v_init_2056_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
v___x_2085_ = lean_array_get_size(v_tail_2082_);
v___x_2086_ = lean_nat_dec_lt(v___x_2059_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v_a_2084_);
lean_dec_ref(v_tail_2082_);
lean_dec(v___x_2054_);
lean_dec_ref(v_f_2053_);
return v___x_2083_;
}
else
{
size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = lean_usize_of_nat(v___x_2085_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2053_, v___x_2054_, v_tail_2082_, v___x_2087_, v___x_2088_, v_a_2084_);
lean_dec_ref(v_tail_2082_);
return v___x_2089_;
}
}
else
{
lean_dec_ref(v_tail_2082_);
lean_dec(v___x_2054_);
lean_dec_ref(v_f_2053_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2090_, lean_object* v_ctx_x3f_2091_, lean_object* v_a_2092_, lean_object* v_x_2093_){
_start:
{
switch(lean_obj_tag(v_x_2093_))
{
case 0:
{
lean_object* v_i_2095_; lean_object* v_t_2096_; lean_object* v___x_2097_; 
v_i_2095_ = lean_ctor_get(v_x_2093_, 0);
lean_inc_ref(v_i_2095_);
v_t_2096_ = lean_ctor_get(v_x_2093_, 1);
lean_inc_ref(v_t_2096_);
lean_dec_ref_known(v_x_2093_, 2);
v___x_2097_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2095_, v_ctx_x3f_2091_);
v_ctx_x3f_2091_ = v___x_2097_;
v_x_2093_ = v_t_2096_;
goto _start;
}
case 1:
{
lean_object* v_i_2099_; lean_object* v_children_2100_; lean_object* v_a_2102_; 
v_i_2099_ = lean_ctor_get(v_x_2093_, 0);
lean_inc_ref(v_i_2099_);
v_children_2100_ = lean_ctor_get(v_x_2093_, 1);
lean_inc_ref(v_children_2100_);
lean_dec_ref_known(v_x_2093_, 2);
if (lean_obj_tag(v_ctx_x3f_2091_) == 0)
{
v_a_2102_ = v_a_2092_;
goto v___jp_2101_;
}
else
{
lean_object* v_val_2106_; lean_object* v___x_2107_; 
v_val_2106_ = lean_ctor_get(v_ctx_x3f_2091_, 0);
lean_inc_ref(v_f_2090_);
lean_inc_ref(v_i_2099_);
lean_inc(v_val_2106_);
v___x_2107_ = lean_apply_4(v_f_2090_, v_val_2106_, v_i_2099_, v_a_2092_, lean_box(0));
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_a_2102_ = v_a_2108_;
goto v___jp_2101_;
}
else
{
lean_dec_ref_known(v_ctx_x3f_2091_, 1);
lean_dec_ref(v_children_2100_);
lean_dec_ref(v_i_2099_);
lean_dec_ref(v_f_2090_);
return v___x_2107_;
}
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2091_, v_i_2099_);
lean_dec_ref(v_i_2099_);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2090_, v___x_2103_, v_children_2100_, v_a_2102_, v___x_2104_);
return v___x_2105_;
}
}
default: 
{
lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_ctx_x3f_2091_);
lean_dec_ref(v_f_2090_);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_x_2093_, 0);
lean_dec(v_unused_2116_);
v___x_2110_ = v_x_2093_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v_x_2093_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 0);
lean_ctor_set(v___x_2110_, 0, v_a_2092_);
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2092_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2117_, lean_object* v___x_2118_, lean_object* v_as_2119_, size_t v_i_2120_, size_t v_stop_2121_, lean_object* v_b_2122_){
_start:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_usize_dec_eq(v_i_2120_, v_stop_2121_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_array_uget_borrowed(v_as_2119_, v_i_2120_);
lean_inc(v___x_2125_);
lean_inc(v___x_2118_);
lean_inc_ref(v_f_2117_);
v___x_2126_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2117_, v___x_2118_, v_b_2122_, v___x_2125_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; size_t v___x_2128_; size_t v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_add(v_i_2120_, v___x_2128_);
v_i_2120_ = v___x_2129_;
v_b_2122_ = v_a_2127_;
goto _start;
}
else
{
lean_dec(v___x_2118_);
lean_dec_ref(v_f_2117_);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2131_; 
lean_dec(v___x_2118_);
lean_dec_ref(v_f_2117_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2122_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_2132_, lean_object* v___x_2133_, lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_){
_start:
{
size_t v_i_boxed_2139_; size_t v_stop_boxed_2140_; lean_object* v_res_2141_; 
v_i_boxed_2139_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_stop_boxed_2140_ = lean_unbox_usize(v_stop_2136_);
lean_dec(v_stop_2136_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2132_, v___x_2133_, v_as_2134_, v_i_boxed_2139_, v_stop_boxed_2140_, v_b_2137_);
lean_dec_ref(v_as_2134_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_2142_, lean_object* v___x_2143_, lean_object* v_as_2144_, lean_object* v_i_2145_, lean_object* v_stop_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_){
_start:
{
size_t v_i_boxed_2149_; size_t v_stop_boxed_2150_; lean_object* v_res_2151_; 
v_i_boxed_2149_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_stop_boxed_2150_ = lean_unbox_usize(v_stop_2146_);
lean_dec(v_stop_2146_);
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2142_, v___x_2143_, v_as_2144_, v_i_boxed_2149_, v_stop_boxed_2150_, v_b_2147_);
lean_dec_ref(v_as_2144_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_2152_, lean_object* v_ctx_x3f_2153_, lean_object* v_a_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2152_, v_ctx_x3f_2153_, v_a_2154_, v_x_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_2158_, lean_object* v___x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2158_, v___x_2159_, v_x_2160_, v_x_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_f_2164_, lean_object* v___x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
size_t v_x_2498__boxed_2171_; size_t v_x_2499__boxed_2172_; lean_object* v_res_2173_; 
v_x_2498__boxed_2171_ = lean_unbox_usize(v_x_2167_);
lean_dec(v_x_2167_);
v_x_2499__boxed_2172_ = lean_unbox_usize(v_x_2168_);
lean_dec(v_x_2168_);
v_res_2173_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2164_, v___x_2165_, v_x_2166_, v_x_2498__boxed_2171_, v_x_2499__boxed_2172_, v_x_2169_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_2174_, lean_object* v___x_2175_, lean_object* v_t_2176_, lean_object* v_init_2177_, lean_object* v_start_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2174_, v___x_2175_, v_t_2176_, v_init_2177_, v_start_2178_);
lean_dec(v_start_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(lean_object* v_f_2181_, lean_object* v_init_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2181_, v___x_2185_, v_init_2182_, v_x_2183_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(lean_object* v_f_2187_, lean_object* v_init_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2187_, v_init_2188_, v_x_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(lean_object* v_f_2192_, lean_object* v_ctx_2193_, lean_object* v_info_2194_, lean_object* v_result_2195_){
_start:
{
if (lean_obj_tag(v_info_2194_) == 1)
{
lean_object* v_i_2197_; lean_object* v___x_2198_; 
v_i_2197_ = lean_ctor_get(v_info_2194_, 0);
lean_inc_ref(v_i_2197_);
lean_dec_ref_known(v_info_2194_, 1);
v___x_2198_ = lean_apply_3(v_f_2192_, v_ctx_2193_, v_i_2197_, lean_box(0));
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2211_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
if (lean_obj_tag(v_a_2199_) == 0)
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_result_2195_);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_result_2195_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
else
{
lean_object* v_val_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v_val_2206_ = lean_ctor_get(v_a_2199_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v_a_2199_, 1);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_val_2206_);
lean_ctor_set(v___x_2207_, 1, v_result_2195_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2207_);
v___x_2209_ = v___x_2201_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_result_2195_);
v_a_2212_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2198_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2198_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_dec_ref(v_info_2194_);
lean_dec_ref(v_ctx_2193_);
lean_dec_ref(v_f_2192_);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v_result_2195_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(lean_object* v_f_2221_, lean_object* v_ctx_2222_, lean_object* v_info_2223_, lean_object* v_result_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_2221_, v_ctx_2222_, v_info_2223_, v_result_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(lean_object* v_t_2227_, lean_object* v_f_2228_){
_start:
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___f_2230_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2230_, 0, v_f_2228_);
v___x_2231_ = lean_box(0);
v___x_2232_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_2230_, v___x_2231_, v_t_2227_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(lean_object* v_t_2233_, lean_object* v_f_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2233_, v_f_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders(lean_object* v_t_2237_, lean_object* v_p_2238_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; 
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2240_, 0, v_p_2238_);
v___x_2241_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2237_, v___f_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___boxed(lean_object* v_t_2242_, lean_object* v_p_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Linter_List_binders(v_t_2242_, v_p_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_object* v_00_u03b1_2246_, lean_object* v_t_2247_, lean_object* v_f_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2247_, v_f_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_t_2252_, lean_object* v_f_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(v_00_u03b1_2251_, v_t_2252_, v_f_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_object* v_00_u03b1_2256_, lean_object* v_f_2257_, lean_object* v_init_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2257_, v_init_2258_, v_x_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_f_2263_, lean_object* v_init_2264_, lean_object* v_x_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_2262_, v_f_2263_, v_init_2264_, v_x_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_2268_, lean_object* v_f_2269_, lean_object* v_ctx_x3f_2270_, lean_object* v_a_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2269_, v_ctx_x3f_2270_, v_a_2271_, v_x_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_f_2276_, lean_object* v_ctx_x3f_2277_, lean_object* v_a_2278_, lean_object* v_x_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_2275_, v_f_2276_, v_ctx_x3f_2277_, v_a_2278_, v_x_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2282_, lean_object* v_f_2283_, lean_object* v___x_2284_, lean_object* v_t_2285_, lean_object* v_init_2286_, lean_object* v_start_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2283_, v___x_2284_, v_t_2285_, v_init_2286_, v_start_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_f_2291_, lean_object* v___x_2292_, lean_object* v_t_2293_, lean_object* v_init_2294_, lean_object* v_start_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_2290_, v_f_2291_, v___x_2292_, v_t_2293_, v_init_2294_, v_start_2295_);
lean_dec(v_start_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2298_, lean_object* v_f_2299_, lean_object* v___x_2300_, lean_object* v_x_2301_, size_t v_x_2302_, size_t v_x_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2299_, v___x_2300_, v_x_2301_, v_x_2302_, v_x_2303_, v_x_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_f_2308_, lean_object* v___x_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v___y_2314_){
_start:
{
size_t v_x_2852__boxed_2315_; size_t v_x_2853__boxed_2316_; lean_object* v_res_2317_; 
v_x_2852__boxed_2315_ = lean_unbox_usize(v_x_2311_);
lean_dec(v_x_2311_);
v_x_2853__boxed_2316_ = lean_unbox_usize(v_x_2312_);
lean_dec(v_x_2312_);
v_res_2317_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_2307_, v_f_2308_, v___x_2309_, v_x_2310_, v_x_2852__boxed_2315_, v_x_2853__boxed_2316_, v_x_2313_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2318_, lean_object* v_f_2319_, lean_object* v___x_2320_, lean_object* v_as_2321_, size_t v_i_2322_, size_t v_stop_2323_, lean_object* v_b_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2319_, v___x_2320_, v_as_2321_, v_i_2322_, v_stop_2323_, v_b_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2327_, lean_object* v_f_2328_, lean_object* v___x_2329_, lean_object* v_as_2330_, lean_object* v_i_2331_, lean_object* v_stop_2332_, lean_object* v_b_2333_, lean_object* v___y_2334_){
_start:
{
size_t v_i_boxed_2335_; size_t v_stop_boxed_2336_; lean_object* v_res_2337_; 
v_i_boxed_2335_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_stop_boxed_2336_ = lean_unbox_usize(v_stop_2332_);
lean_dec(v_stop_2332_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2327_, v_f_2328_, v___x_2329_, v_as_2330_, v_i_boxed_2335_, v_stop_boxed_2336_, v_b_2333_);
lean_dec_ref(v_as_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_2338_, lean_object* v_f_2339_, lean_object* v___x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2339_, v___x_2340_, v_x_2341_, v_x_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_f_2346_, lean_object* v___x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_2345_, v_f_2346_, v___x_2347_, v_x_2348_, v_x_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_2352_, lean_object* v_f_2353_, lean_object* v___x_2354_, lean_object* v_as_2355_, size_t v_i_2356_, size_t v_stop_2357_, lean_object* v_b_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2353_, v___x_2354_, v_as_2355_, v_i_2356_, v_stop_2357_, v_b_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2361_, lean_object* v_f_2362_, lean_object* v___x_2363_, lean_object* v_as_2364_, lean_object* v_i_2365_, lean_object* v_stop_2366_, lean_object* v_b_2367_, lean_object* v___y_2368_){
_start:
{
size_t v_i_boxed_2369_; size_t v_stop_boxed_2370_; lean_object* v_res_2371_; 
v_i_boxed_2369_ = lean_unbox_usize(v_i_2365_);
lean_dec(v_i_2365_);
v_stop_boxed_2370_ = lean_unbox_usize(v_stop_2366_);
lean_dec(v_stop_2366_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_2361_, v_f_2362_, v___x_2363_, v_as_2364_, v_i_boxed_2369_, v_stop_boxed_2370_, v_b_2367_);
lean_dec_ref(v_as_2364_);
return v_res_2371_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(lean_object* v_as_x27_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
if (lean_obj_tag(v_as_x27_2378_) == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_b_2379_);
return v___x_2383_;
}
else
{
lean_object* v_head_2384_; lean_object* v_snd_2385_; lean_object* v_tail_2386_; lean_object* v_fst_2387_; lean_object* v_fst_2388_; lean_object* v_snd_2389_; lean_object* v___x_2390_; 
v_head_2384_ = lean_ctor_get(v_as_x27_2378_, 0);
v_snd_2385_ = lean_ctor_get(v_head_2384_, 1);
v_tail_2386_ = lean_ctor_get(v_as_x27_2378_, 1);
v_fst_2387_ = lean_ctor_get(v_head_2384_, 0);
v_fst_2388_ = lean_ctor_get(v_snd_2385_, 0);
v_snd_2389_ = lean_ctor_get(v_snd_2385_, 1);
v___x_2390_ = lean_box(0);
if (lean_obj_tag(v_fst_2388_) == 1)
{
lean_object* v_str_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_str_2391_ = lean_ctor_get(v_fst_2388_, 1);
lean_inc_ref(v_str_2391_);
v___x_2392_ = l_Lean_Linter_List_stripBinderName(v_str_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Linter_List_allowedArrayNames));
v___x_2394_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2395_ = l_Lean_Linter_List_linter_listVariables;
v___x_2406_ = l_Lean_Expr_getAppNumArgs(v_snd_2389_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_sub(v___x_2406_, v___x_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = l_Lean_Expr_getRevArg_x21(v_snd_2389_, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2411_ = l_Lean_Expr_isAppOf(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2413_ = l_Lean_Expr_isAppOf(v___x_2409_, v___x_2412_);
lean_dec_ref(v___x_2409_);
if (v___x_2413_ == 0)
{
goto v___jp_2396_;
}
else
{
goto v___jp_2402_;
}
}
else
{
lean_dec_ref(v___x_2409_);
goto v___jp_2402_;
}
v___jp_2396_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
v___x_2398_ = l_Lean_stringToMessageData(v___x_2392_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
lean_inc(v_fst_2387_);
v___x_2400_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2395_, v_fst_2387_, v___x_2399_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_dec_ref_known(v___x_2400_, 1);
v_as_x27_2378_ = v_tail_2386_;
v_b_2379_ = v___x_2390_;
goto _start;
}
else
{
return v___x_2400_;
}
}
v___jp_2402_:
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2404_ = lean_string_dec_eq(v___x_2392_, v___x_2403_);
if (v___x_2404_ == 0)
{
goto v___jp_2396_;
}
else
{
lean_dec_ref(v___x_2392_);
v_as_x27_2378_ = v_tail_2386_;
v_b_2379_ = v___x_2390_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2392_);
v_as_x27_2378_ = v_tail_2386_;
v_b_2379_ = v___x_2390_;
goto _start;
}
}
else
{
v_as_x27_2378_ = v_tail_2386_;
v_b_2379_ = v___x_2390_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(lean_object* v_as_x27_2416_, lean_object* v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_2416_, v_b_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_as_x27_2416_);
return v_res_2421_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0));
v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(lean_object* v_as_x27_2428_, lean_object* v_b_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
if (lean_obj_tag(v_as_x27_2428_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_b_2429_);
return v___x_2433_;
}
else
{
lean_object* v_head_2434_; lean_object* v_snd_2435_; lean_object* v_tail_2436_; lean_object* v_fst_2437_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; 
v_head_2434_ = lean_ctor_get(v_as_x27_2428_, 0);
v_snd_2435_ = lean_ctor_get(v_head_2434_, 1);
v_tail_2436_ = lean_ctor_get(v_as_x27_2428_, 1);
v_fst_2437_ = lean_ctor_get(v_head_2434_, 0);
v_fst_2438_ = lean_ctor_get(v_snd_2435_, 0);
v_snd_2439_ = lean_ctor_get(v_snd_2435_, 1);
v___x_2440_ = lean_box(0);
if (lean_obj_tag(v_fst_2438_) == 1)
{
lean_object* v_str_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_str_2441_ = lean_ctor_get(v_fst_2438_, 1);
lean_inc_ref(v_str_2441_);
v___x_2442_ = l_Lean_Linter_List_stripBinderName(v_str_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Linter_List_allowedListNames));
v___x_2444_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2445_ = l_Lean_Linter_List_linter_listVariables;
v___x_2459_ = l_Lean_Expr_getAppNumArgs(v_snd_2439_);
v___x_2460_ = lean_unsigned_to_nat(1u);
v___x_2461_ = lean_nat_sub(v___x_2459_, v___x_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = l_Lean_Expr_getRevArg_x21(v_snd_2439_, v___x_2461_);
v___x_2463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2464_ = l_Lean_Expr_isAppOf(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2466_ = l_Lean_Expr_isAppOf(v___x_2462_, v___x_2465_);
lean_dec_ref(v___x_2462_);
if (v___x_2466_ == 0)
{
goto v___jp_2446_;
}
else
{
goto v___jp_2452_;
}
}
else
{
lean_dec_ref(v___x_2462_);
goto v___jp_2452_;
}
v___jp_2446_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2447_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
v___x_2448_ = l_Lean_stringToMessageData(v___x_2442_);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
lean_inc(v_fst_2437_);
v___x_2450_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2445_, v_fst_2437_, v___x_2449_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_dec_ref_known(v___x_2450_, 1);
v_as_x27_2428_ = v_tail_2436_;
v_b_2429_ = v___x_2440_;
goto _start;
}
else
{
return v___x_2450_;
}
}
v___jp_2452_:
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2));
v___x_2454_ = lean_string_dec_eq(v___x_2442_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2456_ = lean_string_dec_eq(v___x_2442_, v___x_2455_);
if (v___x_2456_ == 0)
{
goto v___jp_2446_;
}
else
{
lean_dec_ref(v___x_2442_);
v_as_x27_2428_ = v_tail_2436_;
v_b_2429_ = v___x_2440_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2442_);
v_as_x27_2428_ = v_tail_2436_;
v_b_2429_ = v___x_2440_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2442_);
v_as_x27_2428_ = v_tail_2436_;
v_b_2429_ = v___x_2440_;
goto _start;
}
}
else
{
v_as_x27_2428_ = v_tail_2436_;
v_b_2429_ = v___x_2440_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(lean_object* v_as_x27_2469_, lean_object* v_b_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_2469_, v_b_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v_as_x27_2469_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
if (lean_obj_tag(v_a_2475_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = l_List_reverse___redArg(v_a_2476_);
return v___x_2477_;
}
else
{
lean_object* v_head_2478_; lean_object* v_snd_2479_; lean_object* v_tail_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2492_; 
v_head_2478_ = lean_ctor_get(v_a_2475_, 0);
lean_inc(v_head_2478_);
v_snd_2479_ = lean_ctor_get(v_head_2478_, 1);
v_tail_2480_ = lean_ctor_get(v_a_2475_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_a_2475_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_a_2475_, 0);
lean_dec(v_unused_2493_);
v___x_2482_ = v_a_2475_;
v_isShared_2483_ = v_isSharedCheck_2492_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_tail_2480_);
lean_dec(v_a_2475_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2492_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_snd_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_snd_2484_ = lean_ctor_get(v_snd_2479_, 1);
v___x_2485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2486_ = l_Lean_Expr_isAppOf(v_snd_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_del_object(v___x_2482_);
lean_dec(v_head_2478_);
v_a_2475_ = v_tail_2480_;
goto _start;
}
else
{
lean_object* v___x_2489_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_a_2476_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_head_2478_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_a_2476_);
v___x_2489_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v_a_2475_ = v_tail_2480_;
v_a_2476_ = v___x_2489_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(uint8_t v___x_2494_, lean_object* v_x_2495_){
_start:
{
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(lean_object* v___x_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v___x_12936__boxed_2498_; uint8_t v_res_2499_; lean_object* v_r_2500_; 
v___x_12936__boxed_2498_ = lean_unbox(v___x_2496_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v___x_12936__boxed_2498_, v_x_2497_);
lean_dec_ref(v_x_2497_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
if (lean_obj_tag(v_a_2501_) == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = l_List_reverse___redArg(v_a_2502_);
return v___x_2503_;
}
else
{
lean_object* v_head_2504_; lean_object* v_snd_2505_; lean_object* v_tail_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2518_; 
v_head_2504_ = lean_ctor_get(v_a_2501_, 0);
lean_inc(v_head_2504_);
v_snd_2505_ = lean_ctor_get(v_head_2504_, 1);
v_tail_2506_ = lean_ctor_get(v_a_2501_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_a_2501_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v_a_2501_, 0);
lean_dec(v_unused_2519_);
v___x_2508_ = v_a_2501_;
v_isShared_2509_ = v_isSharedCheck_2518_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_tail_2506_);
lean_dec(v_a_2501_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2518_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_snd_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_snd_2510_ = lean_ctor_get(v_snd_2505_, 1);
v___x_2511_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2512_ = l_Lean_Expr_isAppOf(v_snd_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_del_object(v___x_2508_);
lean_dec(v_head_2504_);
v_a_2501_ = v_tail_2506_;
goto _start;
}
else
{
lean_object* v___x_2515_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v_a_2502_);
v___x_2515_ = v___x_2508_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_head_2504_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_a_2502_);
v___x_2515_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
v_a_2501_ = v_tail_2506_;
v_a_2502_ = v___x_2515_;
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
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(lean_object* v_as_x27_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
if (lean_obj_tag(v_as_x27_2523_) == 0)
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_b_2524_);
return v___x_2528_;
}
else
{
lean_object* v_head_2529_; lean_object* v_snd_2530_; lean_object* v_tail_2531_; lean_object* v_fst_2532_; lean_object* v_fst_2533_; lean_object* v_snd_2534_; lean_object* v___x_2535_; 
v_head_2529_ = lean_ctor_get(v_as_x27_2523_, 0);
v_snd_2530_ = lean_ctor_get(v_head_2529_, 1);
v_tail_2531_ = lean_ctor_get(v_as_x27_2523_, 1);
v_fst_2532_ = lean_ctor_get(v_head_2529_, 0);
v_fst_2533_ = lean_ctor_get(v_snd_2530_, 0);
v_snd_2534_ = lean_ctor_get(v_snd_2530_, 1);
v___x_2535_ = lean_box(0);
if (lean_obj_tag(v_fst_2533_) == 1)
{
lean_object* v_str_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_str_2536_ = lean_ctor_get(v_fst_2533_, 1);
lean_inc_ref(v_str_2536_);
v___x_2537_ = l_Lean_Linter_List_stripBinderName(v_str_2536_);
v___x_2538_ = ((lean_object*)(l_Lean_Linter_List_allowedVectorNames));
v___x_2539_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2540_ = l_Lean_Linter_List_linter_listVariables;
v___x_2547_ = l_Lean_Expr_getAppNumArgs(v_snd_2534_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_sub(v___x_2547_, v___x_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = l_Lean_Expr_getRevArg_x21(v_snd_2534_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2552_ = l_Lean_Expr_isAppOf(v___x_2550_, v___x_2551_);
lean_dec_ref(v___x_2550_);
if (v___x_2552_ == 0)
{
goto v___jp_2541_;
}
else
{
lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2554_ = lean_string_dec_eq(v___x_2537_, v___x_2553_);
if (v___x_2554_ == 0)
{
goto v___jp_2541_;
}
else
{
lean_dec_ref(v___x_2537_);
v_as_x27_2523_ = v_tail_2531_;
v_b_2524_ = v___x_2535_;
goto _start;
}
}
v___jp_2541_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2542_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
v___x_2543_ = l_Lean_stringToMessageData(v___x_2537_);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_inc(v_fst_2532_);
v___x_2545_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2540_, v_fst_2532_, v___x_2544_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref_known(v___x_2545_, 1);
v_as_x27_2523_ = v_tail_2531_;
v_b_2524_ = v___x_2535_;
goto _start;
}
else
{
return v___x_2545_;
}
}
}
else
{
lean_dec_ref(v___x_2537_);
v_as_x27_2523_ = v_tail_2531_;
v_b_2524_ = v___x_2535_;
goto _start;
}
}
else
{
v_as_x27_2523_ = v_tail_2531_;
v_b_2524_ = v___x_2535_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(lean_object* v_as_x27_2558_, lean_object* v_b_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_2558_, v_b_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v_as_x27_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
if (lean_obj_tag(v_a_2564_) == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = l_List_reverse___redArg(v_a_2565_);
return v___x_2566_;
}
else
{
lean_object* v_head_2567_; lean_object* v_snd_2568_; lean_object* v_tail_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2581_; 
v_head_2567_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_head_2567_);
v_snd_2568_ = lean_ctor_get(v_head_2567_, 1);
v_tail_2569_ = lean_ctor_get(v_a_2564_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v_a_2564_, 0);
lean_dec(v_unused_2582_);
v___x_2571_ = v_a_2564_;
v_isShared_2572_ = v_isSharedCheck_2581_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_tail_2569_);
lean_dec(v_a_2564_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2581_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_snd_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_snd_2573_ = lean_ctor_get(v_snd_2568_, 1);
v___x_2574_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2575_ = l_Lean_Expr_isAppOf(v_snd_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_del_object(v___x_2571_);
lean_dec(v_head_2567_);
v_a_2564_ = v_tail_2569_;
goto _start;
}
else
{
lean_object* v___x_2578_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_a_2565_);
v___x_2578_ = v___x_2571_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_head_2567_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2565_);
v___x_2578_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
v_a_2564_ = v_tail_2569_;
v_a_2565_ = v___x_2578_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(uint8_t v___x_2583_, lean_object* v_as_2584_, size_t v_sz_2585_, size_t v_i_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_usize_dec_lt(v_i_2586_, v_sz_2585_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_b_2587_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___f_2594_; lean_object* v_a_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v_b_2587_);
v___x_2593_ = lean_box(v___x_2583_);
v___f_2594_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2594_, 0, v___x_2593_);
v_a_2595_ = lean_array_uget_borrowed(v_as_2584_, v_i_2586_);
lean_inc(v_a_2595_);
v___x_2596_ = l_Lean_Linter_List_binders(v_a_2595_, v___f_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_n(v_a_2597_, 2);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_box(0);
v___x_2600_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2597_, v___x_2599_);
v___x_2601_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2600_, v___x_2598_, v___y_2588_, v___y_2589_);
lean_dec(v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec_ref_known(v___x_2601_, 1);
lean_inc(v_a_2597_);
v___x_2602_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2597_, v___x_2599_);
v___x_2603_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2602_, v___x_2598_, v___y_2588_, v___y_2589_);
lean_dec(v___x_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2603_, 1);
v___x_2604_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2597_, v___x_2599_);
v___x_2605_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2604_, v___x_2598_, v___y_2588_, v___y_2589_);
lean_dec(v___x_2604_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; size_t v___x_2607_; size_t v___x_2608_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2607_ = ((size_t)1ULL);
v___x_2608_ = lean_usize_add(v_i_2586_, v___x_2607_);
v_i_2586_ = v___x_2608_;
v_b_2587_ = v___x_2606_;
goto _start;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2605_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2605_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_a_2597_);
v_a_2618_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2603_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2603_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_a_2597_);
v_a_2626_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2601_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2601_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2646_; 
v_a_2634_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2636_ = v___x_2596_;
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2596_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_ref_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v_ref_2638_ = lean_ctor_get(v___y_2588_, 7);
v___x_2639_ = lean_io_error_to_string(v_a_2634_);
v___x_2640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
v___x_2641_ = l_Lean_MessageData_ofFormat(v___x_2640_);
lean_inc(v_ref_2638_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v_ref_2638_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2642_);
v___x_2644_ = v___x_2636_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(lean_object* v___x_2647_, lean_object* v_as_2648_, lean_object* v_sz_2649_, lean_object* v_i_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___x_13116__boxed_2655_; size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v___x_13116__boxed_2655_ = lean_unbox(v___x_2647_);
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2649_);
lean_dec(v_sz_2649_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2650_);
lean_dec(v_i_2650_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_13116__boxed_2655_, v_as_2648_, v_sz_boxed_2656_, v_i_boxed_2657_, v_b_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_as_2648_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(uint8_t v___x_2659_, lean_object* v_as_2660_, size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2662_, v_sz_2661_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_b_2663_);
return v___x_2668_;
}
else
{
lean_object* v___x_2669_; lean_object* v___f_2670_; lean_object* v_a_2671_; lean_object* v___x_2672_; 
lean_dec_ref(v_b_2663_);
v___x_2669_ = lean_box(v___x_2659_);
v___f_2670_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2670_, 0, v___x_2669_);
v_a_2671_ = lean_array_uget_borrowed(v_as_2660_, v_i_2662_);
lean_inc(v_a_2671_);
v___x_2672_ = l_Lean_Linter_List_binders(v_a_2671_, v___f_2670_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_n(v_a_2673_, 2);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_box(0);
v___x_2676_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2673_, v___x_2675_);
v___x_2677_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2676_, v___x_2674_, v___y_2664_, v___y_2665_);
lean_dec(v___x_2676_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec_ref_known(v___x_2677_, 1);
lean_inc(v_a_2673_);
v___x_2678_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2673_, v___x_2675_);
v___x_2679_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2678_, v___x_2674_, v___y_2664_, v___y_2665_);
lean_dec(v___x_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec_ref_known(v___x_2679_, 1);
v___x_2680_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2673_, v___x_2675_);
v___x_2681_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2680_, v___x_2674_, v___y_2664_, v___y_2665_);
lean_dec(v___x_2680_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
lean_dec_ref_known(v___x_2681_, 1);
v___x_2682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2683_ = ((size_t)1ULL);
v___x_2684_ = lean_usize_add(v_i_2662_, v___x_2683_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_2659_, v_as_2660_, v_sz_2661_, v___x_2684_, v___x_2682_, v___y_2664_, v___y_2665_);
return v___x_2685_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2681_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2681_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_a_2673_);
v_a_2694_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2679_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2679_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_a_2673_);
v_a_2702_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2677_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2677_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2722_; 
v_a_2710_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2712_ = v___x_2672_;
v_isShared_2713_ = v_isSharedCheck_2722_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2672_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2722_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_ref_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v_ref_2714_ = lean_ctor_get(v___y_2664_, 7);
v___x_2715_ = lean_io_error_to_string(v_a_2710_);
v___x_2716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
v___x_2717_ = l_Lean_MessageData_ofFormat(v___x_2716_);
lean_inc(v_ref_2714_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_ref_2714_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2718_);
v___x_2720_ = v___x_2712_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(lean_object* v___x_2723_, lean_object* v_as_2724_, lean_object* v_sz_2725_, lean_object* v_i_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v___x_13243__boxed_2731_; size_t v_sz_boxed_2732_; size_t v_i_boxed_2733_; lean_object* v_res_2734_; 
v___x_13243__boxed_2731_ = lean_unbox(v___x_2723_);
v_sz_boxed_2732_ = lean_unbox_usize(v_sz_2725_);
lean_dec(v_sz_2725_);
v_i_boxed_2733_ = lean_unbox_usize(v_i_2726_);
lean_dec(v_i_2726_);
v_res_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_13243__boxed_2731_, v_as_2724_, v_sz_boxed_2732_, v_i_boxed_2733_, v_b_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v_as_2724_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(lean_object* v_init_2735_, uint8_t v___x_2736_, lean_object* v_n_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
if (lean_obj_tag(v_n_2737_) == 0)
{
lean_object* v_cs_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; size_t v_sz_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
v_cs_2742_ = lean_ctor_get(v_n_2737_, 0);
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v_b_2738_);
v_sz_2745_ = lean_array_size(v_cs_2742_);
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2735_, v___x_2736_, v_cs_2742_, v_sz_2745_, v___x_2746_, v___x_2744_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2762_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_fst_2752_; 
v_fst_2752_ = lean_ctor_get(v_a_2748_, 0);
if (lean_obj_tag(v_fst_2752_) == 0)
{
lean_object* v_snd_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v_snd_2753_ = lean_ctor_get(v_a_2748_, 1);
lean_inc(v_snd_2753_);
lean_dec(v_a_2748_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_snd_2753_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2754_);
v___x_2756_ = v___x_2750_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
else
{
lean_object* v_val_2758_; lean_object* v___x_2760_; 
lean_inc_ref(v_fst_2752_);
lean_dec(v_a_2748_);
v_val_2758_ = lean_ctor_get(v_fst_2752_, 0);
lean_inc(v_val_2758_);
lean_dec_ref_known(v_fst_2752_, 1);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_val_2758_);
v___x_2760_ = v___x_2750_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_val_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2747_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2747_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_vs_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; size_t v_sz_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v_vs_2771_ = lean_ctor_get(v_n_2737_, 0);
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v_b_2738_);
v_sz_2774_ = lean_array_size(v_vs_2771_);
v___x_2775_ = ((size_t)0ULL);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_2736_, v_vs_2771_, v_sz_2774_, v___x_2775_, v___x_2773_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2791_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2791_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2791_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_fst_2781_; 
v_fst_2781_ = lean_ctor_get(v_a_2777_, 0);
if (lean_obj_tag(v_fst_2781_) == 0)
{
lean_object* v_snd_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v_snd_2782_ = lean_ctor_get(v_a_2777_, 1);
lean_inc(v_snd_2782_);
lean_dec(v_a_2777_);
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_snd_2782_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2783_);
v___x_2785_ = v___x_2779_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v_val_2787_; lean_object* v___x_2789_; 
lean_inc_ref(v_fst_2781_);
lean_dec(v_a_2777_);
v_val_2787_ = lean_ctor_get(v_fst_2781_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v_fst_2781_, 1);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_val_2787_);
v___x_2789_ = v___x_2779_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_val_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2776_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2776_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(lean_object* v_init_2800_, uint8_t v___x_2801_, lean_object* v_as_2802_, size_t v_sz_2803_, size_t v_i_2804_, lean_object* v_b_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_usize_dec_lt(v_i_2804_, v_sz_2803_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2805_);
return v___x_2810_;
}
else
{
lean_object* v_snd_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2845_; 
v_snd_2811_ = lean_ctor_get(v_b_2805_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_b_2805_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_b_2805_, 0);
lean_dec(v_unused_2846_);
v___x_2813_ = v_b_2805_;
v_isShared_2814_ = v_isSharedCheck_2845_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_snd_2811_);
lean_dec(v_b_2805_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2845_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_array_uget_borrowed(v_as_2802_, v_i_2804_);
lean_inc(v_snd_2811_);
v___x_2816_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2800_, v___x_2801_, v_a_2815_, v_snd_2811_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2836_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2836_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2836_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
if (lean_obj_tag(v_a_2817_) == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2817_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2821_);
v___x_2823_ = v___x_2813_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_snd_2811_);
v___x_2823_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2825_ = v___x_2819_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_del_object(v___x_2819_);
lean_dec(v_snd_2811_);
v_a_2828_ = lean_ctor_get(v_a_2817_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v_a_2817_, 1);
v___x_2829_ = lean_box(0);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 1, v_a_2828_);
lean_ctor_set(v___x_2813_, 0, v___x_2829_);
v___x_2831_ = v___x_2813_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2828_);
v___x_2831_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
size_t v___x_2832_; size_t v___x_2833_; 
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2804_, v___x_2832_);
v_i_2804_ = v___x_2833_;
v_b_2805_ = v___x_2831_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_del_object(v___x_2813_);
lean_dec(v_snd_2811_);
v_a_2837_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2816_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2816_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(lean_object* v_init_2847_, lean_object* v___x_2848_, lean_object* v_as_2849_, lean_object* v_sz_2850_, lean_object* v_i_2851_, lean_object* v_b_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v___x_13367__boxed_2856_; size_t v_sz_boxed_2857_; size_t v_i_boxed_2858_; lean_object* v_res_2859_; 
v___x_13367__boxed_2856_ = lean_unbox(v___x_2848_);
v_sz_boxed_2857_ = lean_unbox_usize(v_sz_2850_);
lean_dec(v_sz_2850_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2851_);
lean_dec(v_i_2851_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2847_, v___x_13367__boxed_2856_, v_as_2849_, v_sz_boxed_2857_, v_i_boxed_2858_, v_b_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v_as_2849_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(lean_object* v_init_2860_, lean_object* v___x_2861_, lean_object* v_n_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v___x_13387__boxed_2867_; lean_object* v_res_2868_; 
v___x_13387__boxed_2867_ = lean_unbox(v___x_2861_);
v_res_2868_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2860_, v___x_13387__boxed_2867_, v_n_2862_, v_b_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_n_2862_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(uint8_t v___x_2869_, lean_object* v_as_2870_, size_t v_sz_2871_, size_t v_i_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_usize_dec_lt(v_i_2872_, v_sz_2871_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_b_2873_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___f_2880_; lean_object* v_a_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v_b_2873_);
v___x_2879_ = lean_box(v___x_2869_);
v___f_2880_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2880_, 0, v___x_2879_);
v_a_2881_ = lean_array_uget_borrowed(v_as_2870_, v_i_2872_);
lean_inc(v_a_2881_);
v___x_2882_ = l_Lean_Linter_List_binders(v_a_2881_, v___f_2880_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_n(v_a_2883_, 2);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_box(0);
v___x_2886_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2883_, v___x_2885_);
v___x_2887_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2886_, v___x_2884_, v___y_2874_, v___y_2875_);
lean_dec(v___x_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref_known(v___x_2887_, 1);
lean_inc(v_a_2883_);
v___x_2888_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2883_, v___x_2885_);
v___x_2889_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2888_, v___x_2884_, v___y_2874_, v___y_2875_);
lean_dec(v___x_2888_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec_ref_known(v___x_2889_, 1);
v___x_2890_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2883_, v___x_2885_);
v___x_2891_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2890_, v___x_2884_, v___y_2874_, v___y_2875_);
lean_dec(v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; 
lean_dec_ref_known(v___x_2891_, 1);
v___x_2892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_add(v_i_2872_, v___x_2893_);
v_i_2872_ = v___x_2894_;
v_b_2873_ = v___x_2892_;
goto _start;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2883_);
v_a_2904_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2889_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2889_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2883_);
v_a_2912_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2887_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2887_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2932_; 
v_a_2920_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2922_ = v___x_2882_;
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2882_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_ref_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v_ref_2924_ = lean_ctor_get(v___y_2874_, 7);
v___x_2925_ = lean_io_error_to_string(v_a_2920_);
v___x_2926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
v___x_2927_ = l_Lean_MessageData_ofFormat(v___x_2926_);
lean_inc(v_ref_2924_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v_ref_2924_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2928_);
v___x_2930_ = v___x_2922_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(lean_object* v___x_2933_, lean_object* v_as_2934_, lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_b_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
uint8_t v___x_13571__boxed_2941_; size_t v_sz_boxed_2942_; size_t v_i_boxed_2943_; lean_object* v_res_2944_; 
v___x_13571__boxed_2941_ = lean_unbox(v___x_2933_);
v_sz_boxed_2942_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2943_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_13571__boxed_2941_, v_as_2934_, v_sz_boxed_2942_, v_i_boxed_2943_, v_b_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v_as_2934_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(uint8_t v___x_2945_, lean_object* v_as_2946_, size_t v_sz_2947_, size_t v_i_2948_, lean_object* v_b_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_lt(v_i_2948_, v_sz_2947_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_b_2949_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v___f_2956_; lean_object* v_a_2957_; lean_object* v___x_2958_; 
lean_dec_ref(v_b_2949_);
v___x_2955_ = lean_box(v___x_2945_);
v___f_2956_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2956_, 0, v___x_2955_);
v_a_2957_ = lean_array_uget_borrowed(v_as_2946_, v_i_2948_);
lean_inc(v_a_2957_);
v___x_2958_ = l_Lean_Linter_List_binders(v_a_2957_, v___f_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_n(v_a_2959_, 2);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_box(0);
v___x_2962_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2959_, v___x_2961_);
v___x_2963_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2962_, v___x_2960_, v___y_2950_, v___y_2951_);
lean_dec(v___x_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2963_, 1);
lean_inc(v_a_2959_);
v___x_2964_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2959_, v___x_2961_);
v___x_2965_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2964_, v___x_2960_, v___y_2950_, v___y_2951_);
lean_dec(v___x_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec_ref_known(v___x_2965_, 1);
v___x_2966_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2959_, v___x_2961_);
v___x_2967_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2966_, v___x_2960_, v___y_2950_, v___y_2951_);
lean_dec(v___x_2966_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2969_ = ((size_t)1ULL);
v___x_2970_ = lean_usize_add(v_i_2948_, v___x_2969_);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_2945_, v_as_2946_, v_sz_2947_, v___x_2970_, v___x_2968_, v___y_2950_, v___y_2951_);
return v___x_2971_;
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2967_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2967_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_a_2959_);
v_a_2980_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2965_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2965_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_a_2959_);
v_a_2988_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2963_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2963_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3008_; 
v_a_2996_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2998_ = v___x_2958_;
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2958_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v_ref_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v_ref_3000_ = lean_ctor_get(v___y_2950_, 7);
v___x_3001_ = lean_io_error_to_string(v_a_2996_);
v___x_3002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___x_3003_ = l_Lean_MessageData_ofFormat(v___x_3002_);
lean_inc(v_ref_3000_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_ref_3000_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3004_);
v___x_3006_ = v___x_2998_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(lean_object* v___x_3009_, lean_object* v_as_3010_, lean_object* v_sz_3011_, lean_object* v_i_3012_, lean_object* v_b_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
uint8_t v___x_13698__boxed_3017_; size_t v_sz_boxed_3018_; size_t v_i_boxed_3019_; lean_object* v_res_3020_; 
v___x_13698__boxed_3017_ = lean_unbox(v___x_3009_);
v_sz_boxed_3018_ = lean_unbox_usize(v_sz_3011_);
lean_dec(v_sz_3011_);
v_i_boxed_3019_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_13698__boxed_3017_, v_as_3010_, v_sz_boxed_3018_, v_i_boxed_3019_, v_b_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v_as_3010_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(uint8_t v___x_3021_, lean_object* v_t_3022_, lean_object* v_init_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_root_3027_; lean_object* v_tail_3028_; lean_object* v___x_3029_; 
v_root_3027_ = lean_ctor_get(v_t_3022_, 0);
v_tail_3028_ = lean_ctor_get(v_t_3022_, 1);
v___x_3029_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_3023_, v___x_3021_, v_root_3027_, v_init_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3066_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3066_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3066_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
if (lean_obj_tag(v_a_3030_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; 
v_a_3034_ = lean_ctor_get(v_a_3030_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v_a_3030_, 1);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v_a_3034_);
v___x_3036_ = v___x_3032_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; size_t v_sz_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
lean_del_object(v___x_3032_);
v_a_3038_ = lean_ctor_get(v_a_3030_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v_a_3030_, 1);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_3038_);
v_sz_3041_ = lean_array_size(v_tail_3028_);
v___x_3042_ = ((size_t)0ULL);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_3021_, v_tail_3028_, v_sz_3041_, v___x_3042_, v___x_3040_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3057_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3057_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3057_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v_fst_3048_; 
v_fst_3048_ = lean_ctor_get(v_a_3044_, 0);
if (lean_obj_tag(v_fst_3048_) == 0)
{
lean_object* v_snd_3049_; lean_object* v___x_3051_; 
v_snd_3049_ = lean_ctor_get(v_a_3044_, 1);
lean_inc(v_snd_3049_);
lean_dec(v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_snd_3049_);
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_snd_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
else
{
lean_object* v_val_3053_; lean_object* v___x_3055_; 
lean_inc_ref(v_fst_3048_);
lean_dec(v_a_3044_);
v_val_3053_ = lean_ctor_get(v_fst_3048_, 0);
lean_inc(v_val_3053_);
lean_dec_ref_known(v_fst_3048_, 1);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_val_3053_);
v___x_3055_ = v___x_3046_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3043_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3043_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_a_3067_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3029_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3029_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(lean_object* v___x_3075_, lean_object* v_t_3076_, lean_object* v_init_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v___x_13822__boxed_3081_; lean_object* v_res_3082_; 
v___x_13822__boxed_3081_ = lean_unbox(v___x_3075_);
v_res_3082_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v___x_13822__boxed_3081_, v_t_3076_, v_init_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec_ref(v_t_3076_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0(lean_object* v_stx_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v_scopes_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v_opts_3094_; lean_object* v___x_3095_; lean_object* v_name_3096_; lean_object* v_map_3097_; lean_object* v___x_3098_; 
v___x_3087_ = lean_st_ref_get(v___y_3085_);
v_scopes_3091_ = lean_ctor_get(v___x_3087_, 2);
lean_inc(v_scopes_3091_);
lean_dec(v___x_3087_);
v___x_3092_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3093_ = l_List_head_x21___redArg(v___x_3092_, v_scopes_3091_);
lean_dec(v_scopes_3091_);
v_opts_3094_ = lean_ctor_get(v___x_3093_, 1);
lean_inc_ref(v_opts_3094_);
lean_dec(v___x_3093_);
v___x_3095_ = l_Lean_Linter_List_linter_listVariables;
v_name_3096_ = lean_ctor_get(v___x_3095_, 0);
v_map_3097_ = lean_ctor_get(v_opts_3094_, 0);
lean_inc(v_map_3097_);
lean_dec_ref(v_opts_3094_);
v___x_3098_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3097_, v_name_3096_);
lean_dec(v_map_3097_);
if (lean_obj_tag(v___x_3098_) == 0)
{
goto v___jp_3088_;
}
else
{
lean_object* v_val_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3131_; 
v_val_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3131_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_val_3099_);
lean_dec(v___x_3098_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3131_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
if (lean_obj_tag(v_val_3099_) == 1)
{
uint8_t v_v_3103_; 
v_v_3103_ = lean_ctor_get_uint8(v_val_3099_, 0);
lean_dec_ref_known(v_val_3099_, 0);
if (v_v_3103_ == 0)
{
lean_del_object(v___x_3101_);
goto v___jp_3088_;
}
else
{
lean_object* v___x_3104_; lean_object* v_messages_3105_; uint8_t v___x_3106_; 
v___x_3104_ = lean_st_ref_get(v___y_3085_);
v_messages_3105_ = lean_ctor_get(v___x_3104_, 1);
lean_inc_ref(v_messages_3105_);
lean_dec(v___x_3104_);
v___x_3106_ = l_Lean_MessageLog_hasErrors(v_messages_3105_);
lean_dec_ref(v_messages_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v_infoState_3113_; uint8_t v_enabled_3114_; 
v___x_3107_ = lean_st_ref_get(v___y_3085_);
v_infoState_3113_ = lean_ctor_get(v___x_3107_, 8);
lean_inc_ref(v_infoState_3113_);
lean_dec(v___x_3107_);
v_enabled_3114_ = lean_ctor_get_uint8(v_infoState_3113_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3113_);
if (v_enabled_3114_ == 0)
{
goto v___jp_3108_;
}
else
{
if (v___x_3106_ == 0)
{
lean_object* v___x_3115_; lean_object* v_a_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_del_object(v___x_3101_);
v___x_3115_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_3085_);
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref(v___x_3115_);
v___x_3117_ = lean_box(0);
v___x_3118_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_enabled_3114_, v_a_3116_, v___x_3117_, v___y_3084_, v___y_3085_);
lean_dec(v_a_3116_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3118_, 0);
lean_dec(v_unused_3126_);
v___x_3120_ = v___x_3118_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_dec(v___x_3118_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3117_);
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3117_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
return v___x_3118_;
}
}
else
{
goto v___jp_3108_;
}
}
v___jp_3108_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_box(0);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3109_);
v___x_3111_ = v___x_3101_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(0);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3127_);
v___x_3129_ = v___x_3101_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_del_object(v___x_3101_);
lean_dec(v_val_3099_);
goto v___jp_3088_;
}
}
}
v___jp_3088_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(lean_object* v_stx_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v_stx_3132_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(lean_object* v_as_3150_, lean_object* v_as_x27_3151_, lean_object* v_b_3152_, lean_object* v_a_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_3151_, v_b_3152_, v___y_3154_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(lean_object* v_as_3158_, lean_object* v_as_x27_3159_, lean_object* v_b_3160_, lean_object* v_a_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(v_as_3158_, v_as_x27_3159_, v_b_3160_, v_a_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v_as_x27_3159_);
lean_dec(v_as_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(lean_object* v_as_3166_, lean_object* v_as_x27_3167_, lean_object* v_b_3168_, lean_object* v_a_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_3167_, v_b_3168_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(lean_object* v_as_3174_, lean_object* v_as_x27_3175_, lean_object* v_b_3176_, lean_object* v_a_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(v_as_3174_, v_as_x27_3175_, v_b_3176_, v_a_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v_as_x27_3175_);
lean_dec(v_as_3174_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(lean_object* v_as_3182_, lean_object* v_as_x27_3183_, lean_object* v_b_3184_, lean_object* v_a_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_3183_, v_b_3184_, v___y_3186_, v___y_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(lean_object* v_as_3190_, lean_object* v_as_x27_3191_, lean_object* v_b_3192_, lean_object* v_a_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(v_as_3190_, v_as_x27_3191_, v_b_3192_, v_a_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v_as_x27_3191_);
lean_dec(v_as_3190_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Lean_Linter_List_listVariablesLinter));
v___x_3200_ = l_Lean_Elab_Command_addLinter(v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
return v_res_3202_;
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
