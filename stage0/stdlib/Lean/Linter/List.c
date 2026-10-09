// Lean compiler output
// Module: Lean.Linter.List
// Imports: public import Lean.Linter.Basic public import Lean.Elab.InfoTree.Util import Lean.Linter.Init
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₂"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₃"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "₄"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value;
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
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_60_;
v_res_60_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
return v_res_62_;
}
}
lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_81_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_82_ = ((lean_object*)(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_));
v___x_83_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_80_, v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_84_;
v_res_84_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4____boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__0(lean_object* v_i_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v_i_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__1(lean_object* v_i_90_, lean_object* v_j_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_box(0);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v_j_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v_i_90_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(lean_object* v_i_95_, lean_object* v_stx_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
if (lean_obj_tag(v_a_97_) == 0)
{
lean_object* v___x_99_; 
lean_dec(v_stx_96_);
lean_dec_ref(v_i_95_);
v___x_99_ = lean_array_to_list(v_a_98_);
return v___x_99_;
}
else
{
lean_object* v_head_100_; 
v_head_100_ = lean_ctor_get(v_a_97_, 0);
if (lean_obj_tag(v_head_100_) == 1)
{
lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_116_; 
lean_inc_ref(v_head_100_);
v_tail_101_ = lean_ctor_get(v_a_97_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_97_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v_a_97_, 0);
lean_dec(v_unused_117_);
v___x_103_ = v_a_97_;
v_isShared_104_ = v_isSharedCheck_116_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_dec(v_a_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_116_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_fvarId_105_; lean_object* v_lctx_106_; lean_object* v___x_107_; 
v_fvarId_105_ = lean_ctor_get(v_head_100_, 0);
lean_inc(v_fvarId_105_);
lean_dec_ref_known(v_head_100_, 1);
v_lctx_106_ = lean_ctor_get(v_i_95_, 1);
lean_inc_ref(v_lctx_106_);
v___x_107_ = lean_local_ctx_find(v_lctx_106_, v_fvarId_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_del_object(v___x_103_);
v_a_97_ = v_tail_101_;
goto _start;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_107_, 1);
v___x_110_ = l_Lean_LocalDecl_userName(v_val_109_);
lean_dec(v_val_109_);
lean_inc(v_stx_96_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 0);
lean_ctor_set(v___x_103_, 1, v___x_110_);
lean_ctor_set(v___x_103_, 0, v_stx_96_);
v___x_112_ = v___x_103_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_stx_96_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_115_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; 
v___x_113_ = lean_array_push(v_a_98_, v___x_112_);
v_a_97_ = v_tail_101_;
v_a_98_ = v___x_113_;
goto _start;
}
}
}
}
else
{
lean_object* v_tail_118_; 
v_tail_118_ = lean_ctor_get(v_a_97_, 1);
lean_inc(v_tail_118_);
lean_dec_ref_known(v_a_97_, 2);
v_a_97_ = v_tail_118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2(lean_object* v___f_255_, lean_object* v___f_256_, lean_object* v_x_257_, lean_object* v_info_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_info_258_) == 1)
{
lean_object* v_i_260_; lean_object* v_expr_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_i_260_ = lean_ctor_get(v_info_258_, 0);
lean_inc_ref(v_i_260_);
v_expr_261_ = lean_ctor_get(v_i_260_, 3);
lean_inc_ref(v_expr_261_);
v___x_262_ = l_Lean_Expr_cleanupAnnotations(v_expr_261_);
v___x_263_ = l_Lean_Expr_isApp(v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v___x_262_);
lean_dec_ref_known(v_info_258_, 1);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v_arg_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_arg_265_ = lean_ctor_get(v___x_262_, 1);
lean_inc_ref(v_arg_265_);
v___x_266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_262_);
v___x_267_ = l_Lean_Expr_isApp(v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v___x_266_);
lean_dec_ref(v_arg_265_);
lean_dec_ref_known(v_info_258_, 1);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v_arg_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_arg_269_ = lean_ctor_get(v___x_266_, 1);
lean_inc_ref(v_arg_269_);
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_266_);
v___x_271_ = l_Lean_Expr_isApp(v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v_i_260_);
lean_dec_ref_known(v_info_258_, 1);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_272_ = lean_box(0);
return v___x_272_;
}
else
{
lean_object* v_arg_273_; lean_object* v_stx_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_414_; 
v_arg_273_ = lean_ctor_get(v___x_270_, 1);
lean_inc_ref(v_arg_273_);
v_stx_274_ = l_Lean_Elab_Info_stx(v_info_258_);
v_isSharedCheck_414_ = !lean_is_exclusive(v_info_258_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_info_258_, 0);
lean_dec(v_unused_415_);
v___x_276_ = v_info_258_;
v_isShared_277_ = v_isSharedCheck_414_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_info_258_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_414_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___y_279_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_270_);
v___x_287_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__3));
v___x_288_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__5));
v___x_290_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__7));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__9));
v___x_294_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__11));
v___x_296_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__12));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__14));
v___x_300_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__15));
v___x_302_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__16));
v___x_304_ = l_Lean_Expr_isConstOf(v___x_286_, v___x_303_);
if (v___x_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_Expr_isApp(v___x_286_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec_ref(v___x_286_);
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_306_ = lean_box(0);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_286_);
v___x_308_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__18));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__19));
v___x_311_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__20));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__21));
v___x_315_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__22));
v___x_317_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__24));
v___x_319_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__26));
v___x_321_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__27));
v___x_323_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__29));
v___x_325_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__31));
v___x_327_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__33));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__35));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__36));
v___x_333_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__38));
v___x_335_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__40));
v___x_337_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = l_Lean_Expr_isApp(v___x_307_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec_ref(v___x_307_);
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_307_);
v___x_341_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__41));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__42));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__43));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__44));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__46));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__47));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__49));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__50));
v___x_356_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_340_);
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_360_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__51));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
lean_dec_ref(v___f_256_);
v___x_362_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__52));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__53));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_364_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
lean_dec_ref(v_arg_273_);
v___x_366_ = l_Lean_Expr_isApp(v___x_359_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v___x_359_);
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_255_);
v___x_367_ = lean_box(0);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_359_);
v___x_369_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__56));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_dec_ref(v_arg_265_);
v___x_371_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec_ref(v___x_368_);
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_255_);
v___x_372_ = lean_box(0);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_374_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__59));
v___x_375_ = l_Lean_Expr_isConstOf(v___x_373_, v___x_374_);
lean_dec_ref(v___x_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_i_260_);
lean_dec_ref(v___f_255_);
v___x_376_ = lean_box(0);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_377_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_368_);
lean_dec_ref(v_arg_269_);
v___x_378_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_378_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_359_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
v___x_379_ = lean_apply_1(v___f_255_, v_arg_273_);
v___y_279_ = v___x_379_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_380_; 
lean_dec_ref(v___x_359_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
v___x_380_ = lean_apply_1(v___f_255_, v_arg_273_);
v___y_279_ = v___x_380_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec_ref(v___x_359_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_255_);
v___x_381_ = lean_apply_2(v___f_256_, v_arg_273_, v_arg_269_);
v___y_279_ = v___x_381_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_382_ = lean_apply_1(v___f_255_, v_arg_273_);
v___y_279_ = v___x_382_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_383_ = lean_apply_1(v___f_255_, v_arg_273_);
v___y_279_ = v___x_383_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_384_ = lean_apply_1(v___f_255_, v_arg_273_);
v___y_279_ = v___x_384_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_255_);
v___x_385_ = lean_apply_2(v___f_256_, v_arg_273_, v_arg_269_);
v___y_279_ = v___x_385_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v___f_255_);
v___x_386_ = lean_apply_2(v___f_256_, v_arg_269_, v_arg_265_);
v___y_279_ = v___x_386_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_387_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_387_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_387_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_388_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_388_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_389_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_389_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_390_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_390_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_391_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_391_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_392_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_392_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v___f_255_);
v___x_393_ = lean_apply_2(v___f_256_, v_arg_269_, v_arg_265_);
v___y_279_ = v___x_393_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_394_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_394_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_395_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_395_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_396_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_396_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_397_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_397_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_398_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_398_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_399_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_399_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_399_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_400_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_400_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_400_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_401_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_401_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_402_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_402_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_402_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_403_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_403_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_404_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_404_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_405_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_405_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_265_);
lean_dec_ref(v___f_256_);
v___x_406_ = lean_apply_1(v___f_255_, v_arg_269_);
v___y_279_ = v___x_406_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_407_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_407_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_408_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_408_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_408_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_409_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_409_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_410_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_410_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_411_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_411_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_411_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_412_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_412_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_412_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v___f_256_);
v___x_413_ = lean_apply_1(v___f_255_, v_arg_265_);
v___y_279_ = v___x_413_;
goto v___jp_278_;
}
v___jp_278_:
{
if (lean_obj_tag(v___y_279_) == 0)
{
lean_object* v___x_280_; 
lean_del_object(v___x_276_);
lean_dec(v_stx_274_);
lean_dec_ref(v_i_260_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_282_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_260_, v_stx_274_, v___y_279_, v___x_281_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_282_);
v___x_284_ = v___x_276_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
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
lean_object* v___x_416_; 
lean_dec_ref(v_info_258_);
lean_dec_ref(v___f_256_);
lean_dec_ref(v___f_255_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices___lam__2___boxed(lean_object* v___f_417_, lean_object* v___f_418_, lean_object* v_x_419_, lean_object* v_info_420_, lean_object* v_x_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Linter_List_numericalIndices___lam__2(v___f_417_, v___f_418_, v_x_419_, v_info_420_, v_x_421_);
lean_dec_ref(v_x_421_);
lean_dec_ref(v_x_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
if (lean_obj_tag(v_a_423_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_array_to_list(v_a_424_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v___x_428_; 
v_head_426_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_head_426_);
v_tail_427_ = lean_ctor_get(v_a_423_, 1);
lean_inc(v_tail_427_);
lean_dec_ref_known(v_a_423_, 2);
v___x_428_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_424_, v_head_426_);
v_a_423_ = v_tail_427_;
v_a_424_ = v___x_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalIndices(lean_object* v_t_435_){
_start:
{
lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___f_436_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___closed__2));
v___x_437_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_436_, v_t_435_);
v___x_438_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_439_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__0(lean_object* v_n_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v_n_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1(lean_object* v___f_475_, lean_object* v_x_476_, lean_object* v_info_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_info_477_) == 1)
{
lean_object* v_i_479_; lean_object* v_expr_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_i_479_ = lean_ctor_get(v_info_477_, 0);
lean_inc_ref(v_i_479_);
v_expr_480_ = lean_ctor_get(v_i_479_, 3);
lean_inc_ref(v_expr_480_);
v___x_481_ = l_Lean_Expr_cleanupAnnotations(v_expr_480_);
v___x_482_ = l_Lean_Expr_isApp(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v___x_481_);
lean_dec_ref_known(v_info_477_, 1);
lean_dec_ref(v_i_479_);
lean_dec_ref(v___f_475_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v_arg_484_; lean_object* v_stx_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_536_; 
v_arg_484_ = lean_ctor_get(v___x_481_, 1);
lean_inc_ref(v_arg_484_);
v_stx_485_ = l_Lean_Elab_Info_stx(v_info_477_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_info_477_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_info_477_, 0);
lean_dec(v_unused_537_);
v___x_487_ = v_info_477_;
v_isShared_488_ = v_isSharedCheck_536_;
goto v_resetjp_486_;
}
else
{
lean_dec(v_info_477_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_536_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___y_490_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = l_Lean_Expr_appFnCleanup___redArg(v___x_481_);
v___x_498_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__1));
v___x_499_ = l_Lean_Expr_isConstOf(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__2));
v___x_501_ = l_Lean_Expr_isConstOf(v___x_497_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__3));
v___x_503_ = l_Lean_Expr_isConstOf(v___x_497_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Expr_isApp(v___x_497_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v___x_497_);
lean_del_object(v___x_487_);
lean_dec(v_stx_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_i_479_);
lean_dec_ref(v___f_475_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v_arg_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_arg_506_ = lean_ctor_get(v___x_497_, 1);
lean_inc_ref(v_arg_506_);
v___x_507_ = l_Lean_Expr_appFnCleanup___redArg(v___x_497_);
v___x_508_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_509_ = l_Lean_Expr_isConstOf(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; 
lean_dec_ref(v_arg_484_);
v___x_510_ = l_Lean_Expr_isApp(v___x_507_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v___x_507_);
lean_dec_ref(v_arg_506_);
lean_del_object(v___x_487_);
lean_dec(v_stx_485_);
lean_dec_ref(v_i_479_);
lean_dec_ref(v___f_475_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = l_Lean_Expr_appFnCleanup___redArg(v___x_507_);
v___x_513_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__6));
v___x_514_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__7));
v___x_516_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__8));
v___x_518_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__10));
v___x_520_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__11));
v___x_522_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__12));
v___x_524_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_523_);
lean_dec_ref(v___x_512_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_arg_506_);
lean_del_object(v___x_487_);
lean_dec(v_stx_485_);
lean_dec_ref(v_i_479_);
lean_dec_ref(v___f_475_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_526_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v___x_512_);
v___x_527_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_527_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_512_);
v___x_528_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_528_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_529_; 
lean_dec_ref(v___x_512_);
v___x_529_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_529_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_530_; 
lean_dec_ref(v___x_512_);
v___x_530_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_530_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v___x_512_);
v___x_531_ = lean_apply_1(v___f_475_, v_arg_506_);
v___y_490_ = v___x_531_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v___x_507_);
lean_dec_ref(v_arg_506_);
v___x_532_ = lean_apply_1(v___f_475_, v_arg_484_);
v___y_490_ = v___x_532_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_533_; 
lean_dec_ref(v___x_497_);
v___x_533_ = lean_apply_1(v___f_475_, v_arg_484_);
v___y_490_ = v___x_533_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_497_);
v___x_534_ = lean_apply_1(v___f_475_, v_arg_484_);
v___y_490_ = v___x_534_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v___x_497_);
v___x_535_ = lean_apply_1(v___f_475_, v_arg_484_);
v___y_490_ = v___x_535_;
goto v___jp_489_;
}
v___jp_489_:
{
if (lean_obj_tag(v___y_490_) == 0)
{
lean_object* v___x_491_; 
lean_del_object(v___x_487_);
lean_dec(v_stx_485_);
lean_dec_ref(v_i_479_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_493_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_479_, v_stx_485_, v___y_490_, v___x_492_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_493_);
v___x_495_ = v___x_487_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
else
{
lean_object* v___x_538_; 
lean_dec_ref(v_info_477_);
lean_dec_ref(v___f_475_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths___lam__1___boxed(lean_object* v___f_539_, lean_object* v_x_540_, lean_object* v_info_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Linter_List_numericalWidths___lam__1(v___f_539_, v_x_540_, v_info_541_, v_x_542_);
lean_dec_ref(v_x_542_);
lean_dec_ref(v_x_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_numericalWidths(lean_object* v_t_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___f_548_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___closed__1));
v___x_549_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_548_, v_t_547_);
v___x_550_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_551_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0(lean_object* v_x_555_, lean_object* v_info_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_info_556_) == 1)
{
lean_object* v_i_558_; lean_object* v_expr_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_i_558_ = lean_ctor_get(v_info_556_, 0);
lean_inc_ref(v_i_558_);
v_expr_559_ = lean_ctor_get(v_i_558_, 3);
lean_inc_ref(v_expr_559_);
v___x_560_ = l_Lean_Expr_cleanupAnnotations(v_expr_559_);
v___x_561_ = l_Lean_Expr_isApp(v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v___x_560_);
lean_dec_ref(v_i_558_);
lean_dec_ref_known(v_info_556_, 1);
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v_arg_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_arg_563_ = lean_ctor_get(v___x_560_, 1);
lean_inc_ref(v_arg_563_);
v___x_564_ = l_Lean_Expr_appFnCleanup___redArg(v___x_560_);
v___x_565_ = ((lean_object*)(l_Lean_Linter_List_bitVecWidths___lam__0___closed__1));
v___x_566_ = l_Lean_Expr_isConstOf(v___x_564_, v___x_565_);
lean_dec_ref(v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec_ref(v_arg_563_);
lean_dec_ref(v_i_558_);
lean_dec_ref_known(v_info_556_, 1);
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v_stx_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_579_; 
v_stx_568_ = l_Lean_Elab_Info_stx(v_info_556_);
v_isSharedCheck_579_ = !lean_is_exclusive(v_info_556_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_info_556_, 0);
lean_dec(v_unused_580_);
v___x_570_ = v_info_556_;
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_info_556_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_arg_563_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_575_ = l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(v_i_558_, v_stx_568_, v___x_573_, v___x_574_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_575_);
v___x_577_ = v___x_570_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v___x_581_; 
lean_dec_ref(v_info_556_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths___lam__0___boxed(lean_object* v_x_582_, lean_object* v_info_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Linter_List_bitVecWidths___lam__0(v_x_582_, v_info_583_, v_x_584_);
lean_dec_ref(v_x_584_);
lean_dec_ref(v_x_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_bitVecWidths(lean_object* v_t_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___f_588_ = ((lean_object*)(l_Lean_Linter_List_bitVecWidths___closed__0));
v___x_589_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_588_, v_t_587_);
v___x_590_ = ((lean_object*)(l_Lean_Linter_List_numericalIndices___lam__2___closed__0));
v___x_591_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(lean_object* v_s_593_){
_start:
{
lean_object* v_str_594_; lean_object* v_startInclusive_595_; lean_object* v_endExclusive_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_str_594_ = lean_ctor_get(v_s_593_, 0);
v_startInclusive_595_ = lean_ctor_get(v_s_593_, 1);
v_endExclusive_596_ = lean_ctor_get(v_s_593_, 2);
v___x_597_ = lean_unsigned_to_nat(3u);
v___x_598_ = lean_nat_sub(v_endExclusive_596_, v_startInclusive_595_);
v___x_599_ = lean_nat_dec_le(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v___x_598_);
return v_s_593_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_600_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0));
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_nat_sub(v___x_598_, v___x_597_);
lean_dec(v___x_598_);
v___x_603_ = lean_nat_add(v_startInclusive_595_, v___x_602_);
v___x_604_ = lean_string_memcmp(v_str_594_, v___x_600_, v___x_603_, v___x_601_, v___x_597_);
lean_dec(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v___x_602_);
return v_s_593_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
lean_inc(v_startInclusive_595_);
lean_inc_ref(v_str_594_);
v___x_605_ = l_String_Slice_pos_x21(v_s_593_, v___x_602_);
lean_dec(v___x_602_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_s_593_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_614_ = lean_ctor_get(v_s_593_, 2);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_s_593_, 1);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_s_593_, 0);
lean_dec(v_unused_616_);
v___x_607_ = v_s_593_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_s_593_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_nat_add(v_startInclusive_595_, v___x_605_);
lean_dec(v___x_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_str_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_startInclusive_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(lean_object* v_s_618_){
_start:
{
lean_object* v_str_619_; lean_object* v_startInclusive_620_; lean_object* v_endExclusive_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_str_619_ = lean_ctor_get(v_s_618_, 0);
v_startInclusive_620_ = lean_ctor_get(v_s_618_, 1);
v_endExclusive_621_ = lean_ctor_get(v_s_618_, 2);
v___x_622_ = lean_unsigned_to_nat(3u);
v___x_623_ = lean_nat_sub(v_endExclusive_621_, v_startInclusive_620_);
v___x_624_ = lean_nat_dec_le(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_dec(v___x_623_);
return v_s_618_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_625_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0));
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_nat_sub(v___x_623_, v___x_622_);
lean_dec(v___x_623_);
v___x_628_ = lean_nat_add(v_startInclusive_620_, v___x_627_);
v___x_629_ = lean_string_memcmp(v_str_619_, v___x_625_, v___x_628_, v___x_626_, v___x_622_);
lean_dec(v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v___x_627_);
return v_s_618_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
lean_inc(v_startInclusive_620_);
lean_inc_ref(v_str_619_);
v___x_630_ = l_String_Slice_pos_x21(v_s_618_, v___x_627_);
lean_dec(v___x_627_);
v_isSharedCheck_638_ = !lean_is_exclusive(v_s_618_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_639_ = lean_ctor_get(v_s_618_, 2);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_s_618_, 1);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_s_618_, 0);
lean_dec(v_unused_641_);
v___x_632_ = v_s_618_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_dec(v_s_618_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_nat_add(v_startInclusive_620_, v___x_630_);
lean_dec(v___x_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_str_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_startInclusive_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(lean_object* v_s_643_){
_start:
{
lean_object* v_str_644_; lean_object* v_startInclusive_645_; lean_object* v_endExclusive_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_str_644_ = lean_ctor_get(v_s_643_, 0);
v_startInclusive_645_ = lean_ctor_get(v_s_643_, 1);
v_endExclusive_646_ = lean_ctor_get(v_s_643_, 2);
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = lean_nat_sub(v_endExclusive_646_, v_startInclusive_645_);
v___x_649_ = lean_nat_dec_le(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v___x_648_);
return v_s_643_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_650_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0));
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_nat_sub(v___x_648_, v___x_647_);
lean_dec(v___x_648_);
v___x_653_ = lean_nat_add(v_startInclusive_645_, v___x_652_);
v___x_654_ = lean_string_memcmp(v_str_644_, v___x_650_, v___x_653_, v___x_651_, v___x_647_);
lean_dec(v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v___x_652_);
return v_s_643_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
lean_inc(v_startInclusive_645_);
lean_inc_ref(v_str_644_);
v___x_655_ = l_String_Slice_pos_x21(v_s_643_, v___x_652_);
lean_dec(v___x_652_);
v_isSharedCheck_663_ = !lean_is_exclusive(v_s_643_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; lean_object* v_unused_665_; lean_object* v_unused_666_; 
v_unused_664_ = lean_ctor_get(v_s_643_, 2);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_s_643_, 1);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_s_643_, 0);
lean_dec(v_unused_666_);
v___x_657_ = v_s_643_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_s_643_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_nat_add(v_startInclusive_645_, v___x_655_);
lean_dec(v___x_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_str_644_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_startInclusive_645_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(lean_object* v_s_668_){
_start:
{
lean_object* v_str_669_; lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_str_669_ = lean_ctor_get(v_s_668_, 0);
v_startInclusive_670_ = lean_ctor_get(v_s_668_, 1);
v_endExclusive_671_ = lean_ctor_get(v_s_668_, 2);
v___x_672_ = lean_unsigned_to_nat(3u);
v___x_673_ = lean_nat_sub(v_endExclusive_671_, v_startInclusive_670_);
v___x_674_ = lean_nat_dec_le(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec(v___x_673_);
return v_s_668_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_675_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0));
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_sub(v___x_673_, v___x_672_);
lean_dec(v___x_673_);
v___x_678_ = lean_nat_add(v_startInclusive_670_, v___x_677_);
v___x_679_ = lean_string_memcmp(v_str_669_, v___x_675_, v___x_678_, v___x_676_, v___x_672_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v___x_677_);
return v_s_668_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_startInclusive_670_);
lean_inc_ref(v_str_669_);
v___x_680_ = l_String_Slice_pos_x21(v_s_668_, v___x_677_);
lean_dec(v___x_677_);
v_isSharedCheck_688_ = !lean_is_exclusive(v_s_668_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_689_ = lean_ctor_get(v_s_668_, 2);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_s_668_, 1);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_s_668_, 0);
lean_dec(v_unused_691_);
v___x_682_ = v_s_668_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_dec(v_s_668_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_nat_add(v_startInclusive_670_, v___x_680_);
lean_dec(v___x_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 2, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_str_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_startInclusive_670_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(lean_object* v_s_693_){
_start:
{
lean_object* v_str_694_; lean_object* v_startInclusive_695_; lean_object* v_endExclusive_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_str_694_ = lean_ctor_get(v_s_693_, 0);
v_startInclusive_695_ = lean_ctor_get(v_s_693_, 1);
v_endExclusive_696_ = lean_ctor_get(v_s_693_, 2);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_sub(v_endExclusive_696_, v_startInclusive_695_);
v___x_699_ = lean_nat_dec_le(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v___x_698_);
return v_s_693_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_700_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_nat_sub(v___x_698_, v___x_697_);
lean_dec(v___x_698_);
v___x_703_ = lean_nat_add(v_startInclusive_695_, v___x_702_);
v___x_704_ = lean_string_memcmp(v_str_694_, v___x_700_, v___x_703_, v___x_701_, v___x_697_);
lean_dec(v___x_703_);
if (v___x_704_ == 0)
{
lean_dec(v___x_702_);
return v_s_693_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_startInclusive_695_);
lean_inc_ref(v_str_694_);
v___x_705_ = l_String_Slice_pos_x21(v_s_693_, v___x_702_);
lean_dec(v___x_702_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_s_693_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_714_ = lean_ctor_get(v_s_693_, 2);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_s_693_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_s_693_, 0);
lean_dec(v_unused_716_);
v___x_707_ = v_s_693_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_dec(v_s_693_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_nat_add(v_startInclusive_695_, v___x_705_);
lean_dec(v___x_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 2, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_str_694_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_startInclusive_695_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(lean_object* v_s_717_, lean_object* v_pat_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_string_utf8_byte_size(v_s_717_);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v_s_717_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
v___x_722_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(lean_object* v_s_723_, lean_object* v_pat_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_723_, v_pat_724_);
lean_dec_ref(v_pat_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_stripBinderName(lean_object* v_s_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_str_733_; lean_object* v_startInclusive_734_; lean_object* v_endExclusive_735_; lean_object* v___x_736_; 
v___x_727_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_728_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_726_, v___x_727_);
v___x_729_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(v___x_728_);
v___x_730_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(v___x_729_);
v___x_731_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(v___x_730_);
v___x_732_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(v___x_731_);
v_str_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_ref(v_str_733_);
v_startInclusive_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_startInclusive_734_);
v_endExclusive_735_ = lean_ctor_get(v___x_732_, 2);
lean_inc(v_endExclusive_735_);
lean_dec_ref(v___x_732_);
v___x_736_ = lean_string_utf8_extract_fast(v_str_733_, v_startInclusive_734_, v_endExclusive_735_);
lean_dec(v_endExclusive_735_);
lean_dec(v_startInclusive_734_);
lean_dec_ref(v_str_733_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(lean_object* v_pat_737_, lean_object* v_s_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v_s_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(lean_object* v_pat_740_, lean_object* v_s_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(v_pat_740_, v_s_741_);
lean_dec_ref(v_pat_740_);
return v_res_742_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_infoState_796_; lean_object* v_trees_797_; lean_object* v___x_798_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
v_infoState_796_ = lean_ctor_get(v___x_795_, 8);
lean_inc_ref(v_infoState_796_);
lean_dec(v___x_795_);
v_trees_797_ = lean_ctor_get(v_infoState_796_, 2);
lean_inc_ref(v_trees_797_);
lean_dec_ref(v_infoState_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_trees_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_793_ = stack[0].m_obj;
lean_object* v_res_799_;
v_res_799_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_793_);
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_800_);
lean_dec(v___y_800_);
return v_res_802_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_804_);
return v___x_806_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_803_ = stack[0].m_obj;
lean_object* v___y_804_ = stack[1].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(v___y_803_, v___y_804_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_811_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(lean_object* v_opts_812_, lean_object* v_opt_813_){
_start:
{
lean_object* v_name_814_; lean_object* v_defValue_815_; lean_object* v_map_816_; lean_object* v___x_817_; 
v_name_814_ = lean_ctor_get(v_opt_813_, 0);
v_defValue_815_ = lean_ctor_get(v_opt_813_, 1);
v_map_816_ = lean_ctor_get(v_opts_812_, 0);
v___x_817_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_816_, v_name_814_);
if (lean_obj_tag(v___x_817_) == 0)
{
uint8_t v___x_818_; 
v___x_818_ = lean_unbox(v_defValue_815_);
return v___x_818_;
}
else
{
lean_object* v_val_819_; 
v_val_819_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_817_, 1);
if (lean_obj_tag(v_val_819_) == 1)
{
uint8_t v_v_820_; 
v_v_820_ = lean_ctor_get_uint8(v_val_819_, 0);
lean_dec_ref_known(v_val_819_, 0);
return v_v_820_;
}
else
{
uint8_t v___x_821_; 
lean_dec(v_val_819_);
v___x_821_ = lean_unbox(v_defValue_815_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_812_ = stack[0].m_obj;
lean_object* v_opt_813_ = stack[1].m_obj;
uint8_t v_res_822_;
v_res_822_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_812_, v_opt_813_);
stack->m_num = v_res_822_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_opts_823_, lean_object* v_opt_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_823_, v_opt_824_);
lean_dec_ref(v_opt_824_);
lean_dec_ref(v_opts_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_828_, uint8_t v___y_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 1)
{
lean_object* v_pre_831_; 
v_pre_831_ = lean_ctor_get(v_x_830_, 0);
if (lean_obj_tag(v_pre_831_) == 0)
{
lean_object* v_str_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_str_832_ = lean_ctor_get(v_x_830_, 1);
v___x_833_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_834_ = lean_string_dec_eq(v_str_832_, v___x_833_);
if (v___x_834_ == 0)
{
return v___x_834_;
}
else
{
return v_suppressElabErrors_828_;
}
}
else
{
return v___y_829_;
}
}
else
{
return v___y_829_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_828_ = stack[0].m_num;
uint8_t v___y_829_ = stack[1].m_num;
lean_object* v_x_830_ = stack[2].m_obj;
uint8_t v_res_835_;
v_res_835_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_828_, v___y_829_, v_x_830_);
stack->m_num = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_836_, lean_object* v___y_837_, lean_object* v_x_838_){
_start:
{
uint8_t v_suppressElabErrors_boxed_839_; uint8_t v___y_10937__boxed_840_; uint8_t v_res_841_; lean_object* v_r_842_; 
v_suppressElabErrors_boxed_839_ = lean_unbox(v_suppressElabErrors_836_);
v___y_10937__boxed_840_ = lean_unbox(v___y_837_);
v_res_841_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_839_, v___y_10937__boxed_840_, v_x_838_);
lean_dec(v_x_838_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_843_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_847_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
lean_ctor_set(v___x_849_, 2, v___x_848_);
lean_ctor_set(v___x_849_, 3, v___x_848_);
lean_ctor_set(v___x_849_, 4, v___x_847_);
lean_ctor_set(v___x_849_, 5, v___x_847_);
lean_ctor_set(v___x_849_, 6, v___x_847_);
lean_ctor_set(v___x_849_, 7, v___x_847_);
lean_ctor_set(v___x_849_, 8, v___x_847_);
lean_ctor_set(v___x_849_, 9, v___x_847_);
lean_ctor_set(v___x_849_, 10, v___x_847_);
lean_ctor_set(v___x_849_, 11, v___x_846_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_unsigned_to_nat(32u);
v___x_851_ = lean_mk_empty_array_with_capacity(v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_853_ = ((size_t)5ULL);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_unsigned_to_nat(32u);
v___x_856_ = lean_mk_empty_array_with_capacity(v___x_855_);
v___x_857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3);
v___x_858_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_854_);
lean_ctor_set(v___x_858_, 3, v___x_854_);
lean_ctor_set_usize(v___x_858_, 4, v___x_853_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_859_ = lean_box(1);
v___x_860_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4);
v___x_861_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_859_);
return v___x_862_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(lean_object* v_msgData_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_env_867_; uint8_t v___x_868_; lean_object* v_env_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_scopes_872_; lean_object* v___x_873_; lean_object* v_opts_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_866_ = lean_st_ref_get(v___y_864_);
v_env_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_env_867_);
lean_dec(v___x_866_);
v___x_868_ = 0;
v_env_869_ = l_Lean_Environment_setRecordingDeps(v_env_867_, v___x_868_);
v___x_870_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_871_ = lean_st_ref_get(v___y_864_);
v_scopes_872_ = lean_ctor_get(v___x_871_, 2);
lean_inc(v_scopes_872_);
lean_dec(v___x_871_);
v___x_873_ = l_List_head_x21___redArg(v___x_870_, v_scopes_872_);
lean_dec(v_scopes_872_);
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
lean_ctor_set(v___x_878_, 1, v_msgData_863_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_863_ = stack[0].m_obj;
lean_object* v___y_864_ = stack[1].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_863_, v___y_864_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_msgData_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_881_, v___y_882_);
lean_dec(v___y_882_);
return v_res_884_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(lean_object* v_ref_886_, lean_object* v_msgData_887_, uint8_t v_severity_888_, uint8_t v_isSilent_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; uint8_t v___y_900_; lean_object* v___y_901_; uint8_t v___y_959_; lean_object* v___y_960_; uint8_t v___y_961_; uint8_t v___y_962_; lean_object* v___y_963_; uint8_t v___y_987_; uint8_t v___y_988_; lean_object* v___y_989_; uint8_t v___y_990_; lean_object* v___y_991_; uint8_t v___y_995_; uint8_t v___y_996_; uint8_t v___y_997_; uint8_t v___x_1012_; uint8_t v___y_1014_; uint8_t v___y_1015_; uint8_t v___y_1016_; uint8_t v___y_1018_; uint8_t v___x_1030_; 
v___x_1012_ = 2;
v___x_1030_ = l_Lean_instBEqMessageSeverity_beq(v_severity_888_, v___x_1012_);
if (v___x_1030_ == 0)
{
v___y_1018_ = v___x_1030_;
goto v___jp_1017_;
}
else
{
uint8_t v___x_1031_; 
lean_inc_ref(v_msgData_887_);
v___x_1031_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_887_);
v___y_1018_ = v___x_1031_;
goto v___jp_1017_;
}
v___jp_893_:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_Command_getScope___redArg(v___y_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_currNamespace_904_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_currNamespace_904_ = lean_ctor_get(v_a_903_, 2);
lean_inc(v_currNamespace_904_);
lean_dec(v_a_903_);
v___x_905_ = l_Lean_Elab_Command_getScope___redArg(v___y_901_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_941_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_941_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_941_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_941_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_openDecls_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_env_915_; lean_object* v_messages_916_; lean_object* v_scopes_917_; lean_object* v_usedQuotCtxts_918_; lean_object* v_nextMacroScope_919_; lean_object* v_maxRecDepth_920_; lean_object* v_ngen_921_; lean_object* v_auxDeclNGen_922_; lean_object* v_infoState_923_; lean_object* v_traceState_924_; lean_object* v_snapshotTasks_925_; lean_object* v_prevLinterStates_926_; lean_object* v_codeQualityEntryTasks_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v_openDecls_910_ = lean_ctor_get(v_a_906_, 3);
lean_inc(v_openDecls_910_);
lean_dec(v_a_906_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_currNamespace_904_);
lean_ctor_set(v___x_911_, 1, v_openDecls_910_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___y_897_);
lean_inc_ref(v___y_894_);
lean_inc_ref(v___y_898_);
v___x_913_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_913_, 0, v___y_898_);
lean_ctor_set(v___x_913_, 1, v___y_899_);
lean_ctor_set(v___x_913_, 2, v___y_896_);
lean_ctor_set(v___x_913_, 3, v___y_894_);
lean_ctor_set(v___x_913_, 4, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5, v___y_895_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5 + 1, v___y_900_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5 + 2, v_isSilent_889_);
v___x_914_ = lean_st_ref_take(v___y_901_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
v_messages_916_ = lean_ctor_get(v___x_914_, 1);
v_scopes_917_ = lean_ctor_get(v___x_914_, 2);
v_usedQuotCtxts_918_ = lean_ctor_get(v___x_914_, 3);
v_nextMacroScope_919_ = lean_ctor_get(v___x_914_, 4);
v_maxRecDepth_920_ = lean_ctor_get(v___x_914_, 5);
v_ngen_921_ = lean_ctor_get(v___x_914_, 6);
v_auxDeclNGen_922_ = lean_ctor_get(v___x_914_, 7);
v_infoState_923_ = lean_ctor_get(v___x_914_, 8);
v_traceState_924_ = lean_ctor_get(v___x_914_, 9);
v_snapshotTasks_925_ = lean_ctor_get(v___x_914_, 10);
v_prevLinterStates_926_ = lean_ctor_get(v___x_914_, 11);
v_codeQualityEntryTasks_927_ = lean_ctor_get(v___x_914_, 12);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_940_ == 0)
{
v___x_929_ = v___x_914_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_codeQualityEntryTasks_927_);
lean_inc(v_prevLinterStates_926_);
lean_inc(v_snapshotTasks_925_);
lean_inc(v_traceState_924_);
lean_inc(v_infoState_923_);
lean_inc(v_auxDeclNGen_922_);
lean_inc(v_ngen_921_);
lean_inc(v_maxRecDepth_920_);
lean_inc(v_nextMacroScope_919_);
lean_inc(v_usedQuotCtxts_918_);
lean_inc(v_scopes_917_);
lean_inc(v_messages_916_);
lean_inc(v_env_915_);
lean_dec(v___x_914_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_box(0);
v___x_932_ = l_Lean_MessageLog_add(v___x_913_, v_messages_916_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_env_915_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_scopes_917_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_usedQuotCtxts_918_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_nextMacroScope_919_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v_maxRecDepth_920_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v_ngen_921_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_auxDeclNGen_922_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_infoState_923_);
lean_ctor_set(v_reuseFailAlloc_939_, 9, v_traceState_924_);
lean_ctor_set(v_reuseFailAlloc_939_, 10, v_snapshotTasks_925_);
lean_ctor_set(v_reuseFailAlloc_939_, 11, v_prevLinterStates_926_);
lean_ctor_set(v_reuseFailAlloc_939_, 12, v_codeQualityEntryTasks_927_);
v___x_934_ = v_reuseFailAlloc_939_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_st_ref_put(v___y_901_, v___x_934_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_931_);
v___x_937_ = v___x_908_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_931_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_currNamespace_904_);
lean_dec_ref(v___y_899_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
v_a_942_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_905_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_905_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___y_899_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
v_a_950_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_902_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_902_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_958_:
{
lean_object* v_fileName_964_; lean_object* v_fileMap_965_; uint8_t v_suppressElabErrors_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_985_; 
v_fileName_964_ = lean_ctor_get(v___y_890_, 0);
v_fileMap_965_ = lean_ctor_get(v___y_890_, 1);
v_suppressElabErrors_966_ = lean_ctor_get_uint8(v___y_890_, sizeof(void*)*10);
v___x_967_ = lean_box(v_suppressElabErrors_966_);
v___x_968_ = lean_box(v___y_959_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_969_, 0, v___x_967_);
lean_closure_set(v___f_969_, 1, v___x_968_);
v___x_970_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_887_);
v___x_971_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_970_, v___y_891_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_985_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_985_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_985_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_inc_ref_n(v_fileMap_965_, 2);
v___x_976_ = l_Lean_FileMap_toPosition(v_fileMap_965_, v___y_960_);
lean_dec(v___y_960_);
v___x_977_ = l_Lean_FileMap_toPosition(v_fileMap_965_, v___y_963_);
lean_dec(v___y_963_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_966_ == 0)
{
lean_del_object(v___x_974_);
lean_dec_ref(v___f_969_);
v___y_894_ = v___x_979_;
v___y_895_ = v___y_961_;
v___y_896_ = v___x_978_;
v___y_897_ = v_a_972_;
v___y_898_ = v_fileName_964_;
v___y_899_ = v___x_976_;
v___y_900_ = v___y_962_;
v___y_901_ = v___y_891_;
goto v___jp_893_;
}
else
{
uint8_t v___x_980_; 
lean_inc(v_a_972_);
v___x_980_ = l_Lean_MessageData_hasTag(v___f_969_, v_a_972_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_983_; 
lean_dec_ref_known(v___x_978_, 1);
lean_dec_ref(v___x_976_);
lean_dec(v_a_972_);
v___x_981_ = lean_box(0);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_981_);
v___x_983_ = v___x_974_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
lean_del_object(v___x_974_);
v___y_894_ = v___x_979_;
v___y_895_ = v___y_961_;
v___y_896_ = v___x_978_;
v___y_897_ = v_a_972_;
v___y_898_ = v_fileName_964_;
v___y_899_ = v___x_976_;
v___y_900_ = v___y_962_;
v___y_901_ = v___y_891_;
goto v___jp_893_;
}
}
}
}
v___jp_986_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Syntax_getTailPos_x3f(v___y_989_, v___y_988_);
lean_dec(v___y_989_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_inc(v___y_991_);
v___y_959_ = v___y_987_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_988_;
v___y_962_ = v___y_990_;
v___y_963_ = v___y_991_;
goto v___jp_958_;
}
else
{
lean_object* v_val_993_; 
v_val_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v___x_992_, 1);
v___y_959_ = v___y_987_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_988_;
v___y_962_ = v___y_990_;
v___y_963_ = v_val_993_;
goto v___jp_958_;
}
}
v___jp_994_:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Elab_Command_getRef___redArg(v___y_890_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_ref_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v_ref_1000_ = l_Lean_replaceRef(v_ref_886_, v_a_999_);
lean_dec(v_a_999_);
v___x_1001_ = l_Lean_Syntax_getPos_x3f(v_ref_1000_, v___y_996_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___y_987_ = v___y_995_;
v___y_988_ = v___y_996_;
v___y_989_ = v_ref_1000_;
v___y_990_ = v___y_997_;
v___y_991_ = v___x_1002_;
goto v___jp_986_;
}
else
{
lean_object* v_val_1003_; 
v_val_1003_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v___x_1001_, 1);
v___y_987_ = v___y_995_;
v___y_988_ = v___y_996_;
v___y_989_ = v_ref_1000_;
v___y_990_ = v___y_997_;
v___y_991_ = v_val_1003_;
goto v___jp_986_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_msgData_887_);
v_a_1004_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_998_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
v___jp_1013_:
{
if (v___y_1016_ == 0)
{
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1015_;
v___y_997_ = v_severity_888_;
goto v___jp_994_;
}
else
{
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1015_;
v___y_997_ = v___x_1012_;
goto v___jp_994_;
}
}
v___jp_1017_:
{
if (v___y_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_scopes_1021_; lean_object* v___x_1022_; lean_object* v_opts_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1019_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1020_ = lean_st_ref_get(v___y_891_);
v_scopes_1021_ = lean_ctor_get(v___x_1020_, 2);
lean_inc(v_scopes_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = l_List_head_x21___redArg(v___x_1019_, v_scopes_1021_);
lean_dec(v_scopes_1021_);
v_opts_1023_ = lean_ctor_get(v___x_1022_, 1);
lean_inc_ref(v_opts_1023_);
lean_dec(v___x_1022_);
v___x_1024_ = 1;
v___x_1025_ = l_Lean_instBEqMessageSeverity_beq(v_severity_888_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec_ref(v_opts_1023_);
v___y_1014_ = v___y_1018_;
v___y_1015_ = v___y_1018_;
v___y_1016_ = v___x_1025_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = l_Lean_warningAsError;
v___x_1027_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_1023_, v___x_1026_);
lean_dec_ref(v_opts_1023_);
v___y_1014_ = v___y_1018_;
v___y_1015_ = v___y_1018_;
v___y_1016_ = v___x_1027_;
goto v___jp_1013_;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_msgData_887_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_886_ = stack[0].m_obj;
lean_object* v_msgData_887_ = stack[1].m_obj;
uint8_t v_severity_888_ = stack[2].m_num;
uint8_t v_isSilent_889_ = stack[3].m_num;
lean_object* v___y_890_ = stack[4].m_obj;
lean_object* v___y_891_ = stack[5].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_886_, v_msgData_887_, v_severity_888_, v_isSilent_889_, v___y_890_, v___y_891_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1033_, lean_object* v_msgData_1034_, lean_object* v_severity_1035_, lean_object* v_isSilent_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_severity_boxed_1040_; uint8_t v_isSilent_boxed_1041_; lean_object* v_res_1042_; 
v_severity_boxed_1040_ = lean_unbox(v_severity_1035_);
v_isSilent_boxed_1041_ = lean_unbox(v_isSilent_1036_);
v_res_1042_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1033_, v_msgData_1034_, v_severity_boxed_1040_, v_isSilent_boxed_1041_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_ref_1033_);
return v_res_1042_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(lean_object* v_ref_1043_, lean_object* v_msgData_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = 1;
v___x_1049_ = 0;
v___x_1050_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1043_, v_msgData_1044_, v___x_1048_, v___x_1049_, v___y_1045_, v___y_1046_);
return v___x_1050_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1043_ = stack[0].m_obj;
lean_object* v_msgData_1044_ = stack[1].m_obj;
lean_object* v___y_1045_ = stack[2].m_obj;
lean_object* v___y_1046_ = stack[3].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_1043_, v_msgData_1044_, v___y_1045_, v___y_1046_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(lean_object* v_ref_1052_, lean_object* v_msgData_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_1052_, v_msgData_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_ref_1052_);
return v_res_1057_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(lean_object* v_linterOption_1064_, lean_object* v_stx_1065_, lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_name_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1088_; 
v_name_1070_ = lean_ctor_get(v_linterOption_1064_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_linterOption_1064_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_linterOption_1064_, 1);
lean_dec(v_unused_1089_);
v___x_1072_ = v_linterOption_1064_;
v_isShared_1073_ = v_isSharedCheck_1088_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_name_1070_);
lean_dec(v_linterOption_1064_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1088_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
lean_inc(v_name_1070_);
v___x_1075_ = l_Lean_MessageData_ofName(v_name_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 7);
lean_ctor_set(v___x_1072_, 1, v___x_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_disable_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1078_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v_disable_1080_ = l_Lean_MessageData_note(v___x_1079_);
v___x_1081_ = l_Lean_Linter_linterMessageTag;
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_msg_1066_);
lean_ctor_set(v___x_1082_, 1, v_disable_1080_);
v___x_1083_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_name_1070_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
lean_inc(v_stx_1065_);
v___x_1085_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_stx_1065_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_1065_, v___x_1085_, v___y_1067_, v___y_1068_);
lean_dec(v_stx_1065_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_1064_ = stack[0].m_obj;
lean_object* v_stx_1065_ = stack[1].m_obj;
lean_object* v_msg_1066_ = stack[2].m_obj;
lean_object* v___y_1067_ = stack[3].m_obj;
lean_object* v___y_1068_ = stack[4].m_obj;
lean_object* v_res_1090_;
v_res_1090_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v_linterOption_1064_, v_stx_1065_, v_msg_1066_, v___y_1067_, v___y_1068_);
stack->m_obj
 = v_res_1090_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(lean_object* v_linterOption_1091_, lean_object* v_stx_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v_linterOption_1091_, v_stx_1092_, v_msg_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
uint8_t l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(lean_object* v_a_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = 0;
return v___x_1100_;
}
else
{
lean_object* v_head_1101_; lean_object* v_tail_1102_; uint8_t v___x_1103_; 
v_head_1101_ = lean_ctor_get(v_x_1099_, 0);
v_tail_1102_ = lean_ctor_get(v_x_1099_, 1);
v___x_1103_ = lean_string_dec_eq(v_a_1098_, v_head_1101_);
if (v___x_1103_ == 0)
{
v_x_1099_ = v_tail_1102_;
goto _start;
}
else
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1098_ = stack[0].m_obj;
lean_object* v_x_1099_ = stack[1].m_obj;
uint8_t v_res_1105_;
v_res_1105_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_1098_, v_x_1099_);
stack->m_num = v_res_1105_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(lean_object* v_a_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_1106_, v_x_1107_);
lean_dec(v_x_1107_);
lean_dec_ref(v_a_1106_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(lean_object* v_as_x27_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
if (lean_obj_tag(v_as_x27_1113_) == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_b_1114_);
return v___x_1118_;
}
else
{
lean_object* v_head_1119_; lean_object* v_tail_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1123_; 
v_head_1119_ = lean_ctor_get(v_as_x27_1113_, 0);
v_tail_1120_ = lean_ctor_get(v_as_x27_1113_, 1);
v_fst_1121_ = lean_ctor_get(v_head_1119_, 0);
v_snd_1122_ = lean_ctor_get(v_head_1119_, 1);
v___x_1123_ = lean_box(0);
if (lean_obj_tag(v_snd_1122_) == 1)
{
lean_object* v_str_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_str_1124_ = lean_ctor_get(v_snd_1122_, 1);
v___x_1125_ = ((lean_object*)(l_Lean_Linter_List_allowedWidths));
lean_inc_ref(v_str_1124_);
v___x_1126_ = l_Lean_Linter_List_stripBinderName(v_str_1124_);
v___x_1127_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1126_, v___x_1125_);
lean_dec_ref(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1129_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
lean_inc_ref(v_str_1124_);
v___x_1130_ = l_Lean_stringToMessageData(v_str_1124_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
lean_inc(v_fst_1121_);
v___x_1132_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1128_, v_fst_1121_, v___x_1131_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_dec_ref_known(v___x_1132_, 1);
v_as_x27_1113_ = v_tail_1120_;
v_b_1114_ = v___x_1123_;
goto _start;
}
else
{
return v___x_1132_;
}
}
else
{
v_as_x27_1113_ = v_tail_1120_;
v_b_1114_ = v___x_1123_;
goto _start;
}
}
else
{
v_as_x27_1113_ = v_tail_1120_;
v_b_1114_ = v___x_1123_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1113_ = stack[0].m_obj;
lean_object* v_b_1114_ = stack[1].m_obj;
lean_object* v___y_1115_ = stack[2].m_obj;
lean_object* v___y_1116_ = stack[3].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1113_, v_b_1114_, v___y_1115_, v___y_1116_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(lean_object* v_as_x27_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1137_, v_b_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v_as_x27_1137_);
return v_res_1142_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(lean_object* v_as_x27_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
if (lean_obj_tag(v_as_x27_1146_) == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_b_1147_);
return v___x_1151_;
}
else
{
lean_object* v_head_1152_; lean_object* v_tail_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; 
v_head_1152_ = lean_ctor_get(v_as_x27_1146_, 0);
v_tail_1153_ = lean_ctor_get(v_as_x27_1146_, 1);
v_fst_1154_ = lean_ctor_get(v_head_1152_, 0);
v_snd_1155_ = lean_ctor_get(v_head_1152_, 1);
v___x_1156_ = lean_box(0);
if (lean_obj_tag(v_snd_1155_) == 1)
{
lean_object* v_str_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_str_1157_ = lean_ctor_get(v_snd_1155_, 1);
v___x_1158_ = ((lean_object*)(l_Lean_Linter_List_allowedBitVecWidths));
lean_inc_ref(v_str_1157_);
v___x_1159_ = l_Lean_Linter_List_stripBinderName(v_str_1157_);
v___x_1160_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1159_, v___x_1158_);
lean_dec_ref(v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1161_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1162_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
lean_inc_ref(v_str_1157_);
v___x_1163_ = l_Lean_stringToMessageData(v_str_1157_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
lean_inc(v_fst_1154_);
v___x_1165_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1161_, v_fst_1154_, v___x_1164_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_dec_ref_known(v___x_1165_, 1);
v_as_x27_1146_ = v_tail_1153_;
v_b_1147_ = v___x_1156_;
goto _start;
}
else
{
return v___x_1165_;
}
}
else
{
v_as_x27_1146_ = v_tail_1153_;
v_b_1147_ = v___x_1156_;
goto _start;
}
}
else
{
v_as_x27_1146_ = v_tail_1153_;
v_b_1147_ = v___x_1156_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1146_ = stack[0].m_obj;
lean_object* v_b_1147_ = stack[1].m_obj;
lean_object* v___y_1148_ = stack[2].m_obj;
lean_object* v___y_1149_ = stack[3].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1146_, v_b_1147_, v___y_1148_, v___y_1149_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(lean_object* v_as_x27_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1170_, v_b_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_as_x27_1170_);
return v_res_1175_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(lean_object* v_as_x27_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v_as_x27_1179_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1180_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1189_; 
v_head_1185_ = lean_ctor_get(v_as_x27_1179_, 0);
v_tail_1186_ = lean_ctor_get(v_as_x27_1179_, 1);
v_fst_1187_ = lean_ctor_get(v_head_1185_, 0);
v_snd_1188_ = lean_ctor_get(v_head_1185_, 1);
v___x_1189_ = lean_box(0);
if (lean_obj_tag(v_snd_1188_) == 1)
{
lean_object* v_str_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_str_1190_ = lean_ctor_get(v_snd_1188_, 1);
v___x_1191_ = ((lean_object*)(l_Lean_Linter_List_allowedIndices));
lean_inc_ref(v_str_1190_);
v___x_1192_ = l_Lean_Linter_List_stripBinderName(v_str_1190_);
v___x_1193_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1192_, v___x_1191_);
lean_dec_ref(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1194_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1195_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
lean_inc_ref(v_str_1190_);
v___x_1196_ = l_Lean_stringToMessageData(v_str_1190_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
lean_inc(v_fst_1187_);
v___x_1198_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1194_, v_fst_1187_, v___x_1197_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_dec_ref_known(v___x_1198_, 1);
v_as_x27_1179_ = v_tail_1186_;
v_b_1180_ = v___x_1189_;
goto _start;
}
else
{
return v___x_1198_;
}
}
else
{
v_as_x27_1179_ = v_tail_1186_;
v_b_1180_ = v___x_1189_;
goto _start;
}
}
else
{
v_as_x27_1179_ = v_tail_1186_;
v_b_1180_ = v___x_1189_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1179_ = stack[0].m_obj;
lean_object* v_b_1180_ = stack[1].m_obj;
lean_object* v___y_1181_ = stack[2].m_obj;
lean_object* v___y_1182_ = stack[3].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1179_, v_b_1180_, v___y_1181_, v___y_1182_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(lean_object* v_as_x27_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1203_, v_b_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v_as_x27_1203_);
return v_res_1208_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(lean_object* v_as_1212_, size_t v_sz_1213_, size_t v_i_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_usize_dec_lt(v_i_1214_, v_sz_1213_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_b_1215_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_b_1215_);
v___x_1221_ = lean_box(0);
v_a_1222_ = lean_array_uget_borrowed(v_as_1212_, v_i_1214_);
lean_inc(v_a_1222_);
v___x_1223_ = l_Lean_Linter_List_numericalIndices(v_a_1222_);
v___x_1224_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1223_, v___x_1221_, v___y_1216_, v___y_1217_);
lean_dec(v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1224_, 1);
lean_inc(v_a_1222_);
v___x_1225_ = l_Lean_Linter_List_numericalWidths(v_a_1222_);
v___x_1226_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1225_, v___x_1221_, v___y_1216_, v___y_1217_);
lean_dec(v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref_known(v___x_1226_, 1);
lean_inc(v_a_1222_);
v___x_1227_ = l_Lean_Linter_List_bitVecWidths(v_a_1222_);
v___x_1228_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1227_, v___x_1221_, v___y_1216_, v___y_1217_);
lean_dec(v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; 
lean_dec_ref_known(v___x_1228_, 1);
v___x_1229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1214_, v___x_1230_);
v_i_1214_ = v___x_1231_;
v_b_1215_ = v___x_1229_;
goto _start;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1228_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1228_);
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
v_a_1241_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1226_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1226_);
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
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_a_1249_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1224_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1224_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1212_ = stack[0].m_obj;
size_t v_sz_1213_ = stack[1].m_num;
size_t v_i_1214_ = stack[2].m_num;
lean_object* v_b_1215_ = stack[3].m_obj;
lean_object* v___y_1216_ = stack[4].m_obj;
lean_object* v___y_1217_ = stack[5].m_obj;
lean_object* v_res_1257_;
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1212_, v_sz_1213_, v_i_1214_, v_b_1215_, v___y_1216_, v___y_1217_);
stack->m_obj
 = v_res_1257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(lean_object* v_as_1258_, lean_object* v_sz_1259_, lean_object* v_i_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1259_);
lean_dec(v_sz_1259_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1258_, v_sz_boxed_1265_, v_i_boxed_1266_, v_b_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v_as_1258_);
return v_res_1267_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_b_1271_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v_b_1271_);
v___x_1277_ = lean_box(0);
v_a_1278_ = lean_array_uget_borrowed(v_as_1268_, v_i_1270_);
lean_inc(v_a_1278_);
v___x_1279_ = l_Lean_Linter_List_numericalIndices(v_a_1278_);
v___x_1280_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1279_, v___x_1277_, v___y_1272_, v___y_1273_);
lean_dec(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref_known(v___x_1280_, 1);
lean_inc(v_a_1278_);
v___x_1281_ = l_Lean_Linter_List_numericalWidths(v_a_1278_);
v___x_1282_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1281_, v___x_1277_, v___y_1272_, v___y_1273_);
lean_dec(v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1282_, 1);
lean_inc(v_a_1278_);
v___x_1283_ = l_Lean_Linter_List_bitVecWidths(v_a_1278_);
v___x_1284_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1283_, v___x_1277_, v___y_1272_, v___y_1273_);
lean_dec(v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1284_, 1);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_add(v_i_1270_, v___x_1286_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1268_, v_sz_1269_, v___x_1287_, v___x_1285_, v___y_1272_, v___y_1273_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1284_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1284_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_a_1297_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1282_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1282_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1280_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1280_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1268_ = stack[0].m_obj;
size_t v_sz_1269_ = stack[1].m_num;
size_t v_i_1270_ = stack[2].m_num;
lean_object* v_b_1271_ = stack[3].m_obj;
lean_object* v___y_1272_ = stack[4].m_obj;
lean_object* v___y_1273_ = stack[5].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_1268_, v_sz_1269_, v_i_1270_, v_b_1271_, v___y_1272_, v___y_1273_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_as_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_1314_, v_sz_boxed_1321_, v_i_boxed_1322_, v_b_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_as_1314_);
return v_res_1323_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(lean_object* v_init_1324_, lean_object* v_n_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
if (lean_obj_tag(v_n_1325_) == 0)
{
lean_object* v_cs_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; size_t v_sz_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v_cs_1330_ = lean_ctor_get(v_n_1325_, 0);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v_b_1326_);
v_sz_1333_ = lean_array_size(v_cs_1330_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1324_, v_cs_1330_, v_sz_1333_, v___x_1334_, v___x_1332_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1350_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_fst_1340_; 
v_fst_1340_ = lean_ctor_get(v_a_1336_, 0);
if (lean_obj_tag(v_fst_1340_) == 0)
{
lean_object* v_snd_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v_snd_1341_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_snd_1341_);
lean_dec(v_a_1336_);
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_snd_1341_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1342_);
v___x_1344_ = v___x_1338_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_object* v_val_1346_; lean_object* v___x_1348_; 
lean_inc_ref(v_fst_1340_);
lean_dec(v_a_1336_);
v_val_1346_ = lean_ctor_get(v_fst_1340_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v_fst_1340_, 1);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_val_1346_);
v___x_1348_ = v___x_1338_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_val_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1335_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1335_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_vs_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; size_t v_sz_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v_vs_1359_ = lean_ctor_get(v_n_1325_, 0);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v_b_1326_);
v_sz_1362_ = lean_array_size(v_vs_1359_);
v___x_1363_ = ((size_t)0ULL);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_1359_, v_sz_1362_, v___x_1363_, v___x_1361_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1379_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1379_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1379_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_fst_1369_; 
v_fst_1369_ = lean_ctor_get(v_a_1365_, 0);
if (lean_obj_tag(v_fst_1369_) == 0)
{
lean_object* v_snd_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_snd_1370_ = lean_ctor_get(v_a_1365_, 1);
lean_inc(v_snd_1370_);
lean_dec(v_a_1365_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_snd_1370_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1371_);
v___x_1373_ = v___x_1367_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1377_; 
lean_inc_ref(v_fst_1369_);
lean_dec(v_a_1365_);
v_val_1375_ = lean_ctor_get(v_fst_1369_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v_fst_1369_, 1);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_val_1375_);
v___x_1377_ = v___x_1367_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1364_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1364_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1324_ = stack[0].m_obj;
lean_object* v_n_1325_ = stack[1].m_obj;
lean_object* v_b_1326_ = stack[2].m_obj;
lean_object* v___y_1327_ = stack[3].m_obj;
lean_object* v___y_1328_ = stack[4].m_obj;
lean_object* v_res_1388_;
v_res_1388_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1324_, v_n_1325_, v_b_1326_, v___y_1327_, v___y_1328_);
stack->m_obj
 = v_res_1388_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(lean_object* v_init_1389_, lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_b_1393_);
return v___x_1398_;
}
else
{
lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1433_; 
v_snd_1399_ = lean_ctor_get(v_b_1393_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_b_1393_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_b_1393_, 0);
lean_dec(v_unused_1434_);
v___x_1401_ = v_b_1393_;
v_isShared_1402_ = v_isSharedCheck_1433_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_dec(v_b_1393_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1433_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v_a_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(0);
v_a_1404_ = lean_array_uget_borrowed(v_as_1390_, v_i_1392_);
lean_inc(v_snd_1399_);
v___x_1405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1389_, v_a_1404_, v_snd_1399_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1424_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1424_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1424_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
if (lean_obj_tag(v_a_1406_) == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1406_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1410_);
v___x_1412_ = v___x_1401_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_snd_1399_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1412_);
v___x_1414_ = v___x_1408_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; 
lean_del_object(v___x_1408_);
lean_dec(v_snd_1399_);
v_a_1417_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v_a_1406_, 1);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_a_1417_);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1419_ = v___x_1401_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1417_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
size_t v___x_1420_; size_t v___x_1421_; 
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1392_, v___x_1420_);
v_i_1392_ = v___x_1421_;
v_b_1393_ = v___x_1419_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_del_object(v___x_1401_);
lean_dec(v_snd_1399_);
v_a_1425_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1405_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1405_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1389_ = stack[0].m_obj;
lean_object* v_as_1390_ = stack[1].m_obj;
size_t v_sz_1391_ = stack[2].m_num;
size_t v_i_1392_ = stack[3].m_num;
lean_object* v_b_1393_ = stack[4].m_obj;
lean_object* v___y_1394_ = stack[5].m_obj;
lean_object* v___y_1395_ = stack[6].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1389_, v_as_1390_, v_sz_1391_, v_i_1392_, v_b_1393_, v___y_1394_, v___y_1395_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(lean_object* v_init_1436_, lean_object* v_as_1437_, lean_object* v_sz_1438_, lean_object* v_i_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
size_t v_sz_boxed_1444_; size_t v_i_boxed_1445_; lean_object* v_res_1446_; 
v_sz_boxed_1444_ = lean_unbox_usize(v_sz_1438_);
lean_dec(v_sz_1438_);
v_i_boxed_1445_ = lean_unbox_usize(v_i_1439_);
lean_dec(v_i_1439_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1436_, v_as_1437_, v_sz_boxed_1444_, v_i_boxed_1445_, v_b_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_as_1437_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(lean_object* v_init_1447_, lean_object* v_n_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1447_, v_n_1448_, v_b_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v_n_1448_);
return v_res_1453_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(lean_object* v_as_1457_, size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_usize_dec_lt(v_i_1459_, v_sz_1458_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1460_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_b_1460_);
v___x_1466_ = lean_box(0);
v_a_1467_ = lean_array_uget_borrowed(v_as_1457_, v_i_1459_);
lean_inc(v_a_1467_);
v___x_1468_ = l_Lean_Linter_List_numericalIndices(v_a_1467_);
v___x_1469_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1468_, v___x_1466_, v___y_1461_, v___y_1462_);
lean_dec(v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref_known(v___x_1469_, 1);
lean_inc(v_a_1467_);
v___x_1470_ = l_Lean_Linter_List_numericalWidths(v_a_1467_);
v___x_1471_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1470_, v___x_1466_, v___y_1461_, v___y_1462_);
lean_dec(v___x_1470_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref_known(v___x_1471_, 1);
lean_inc(v_a_1467_);
v___x_1472_ = l_Lean_Linter_List_bitVecWidths(v_a_1467_);
v___x_1473_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1472_, v___x_1466_, v___y_1461_, v___y_1462_);
lean_dec(v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; 
lean_dec_ref_known(v___x_1473_, 1);
v___x_1474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1459_, v___x_1475_);
v_i_1459_ = v___x_1476_;
v_b_1460_ = v___x_1474_;
goto _start;
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1473_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1471_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1471_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_a_1494_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1469_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1469_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1457_ = stack[0].m_obj;
size_t v_sz_1458_ = stack[1].m_num;
size_t v_i_1459_ = stack[2].m_num;
lean_object* v_b_1460_ = stack[3].m_obj;
lean_object* v___y_1461_ = stack[4].m_obj;
lean_object* v___y_1462_ = stack[5].m_obj;
lean_object* v_res_1502_;
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1457_, v_sz_1458_, v_i_1459_, v_b_1460_, v___y_1461_, v___y_1462_);
stack->m_obj
 = v_res_1502_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(lean_object* v_as_1503_, lean_object* v_sz_1504_, lean_object* v_i_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
size_t v_sz_boxed_1510_; size_t v_i_boxed_1511_; lean_object* v_res_1512_; 
v_sz_boxed_1510_ = lean_unbox_usize(v_sz_1504_);
lean_dec(v_sz_1504_);
v_i_boxed_1511_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1503_, v_sz_boxed_1510_, v_i_boxed_1511_, v_b_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_as_1503_);
return v_res_1512_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(lean_object* v_as_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_b_1516_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_b_1516_);
v___x_1522_ = lean_box(0);
v_a_1523_ = lean_array_uget_borrowed(v_as_1513_, v_i_1515_);
lean_inc(v_a_1523_);
v___x_1524_ = l_Lean_Linter_List_numericalIndices(v_a_1523_);
v___x_1525_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1524_, v___x_1522_, v___y_1517_, v___y_1518_);
lean_dec(v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref_known(v___x_1525_, 1);
lean_inc(v_a_1523_);
v___x_1526_ = l_Lean_Linter_List_numericalWidths(v_a_1523_);
v___x_1527_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1526_, v___x_1522_, v___y_1517_, v___y_1518_);
lean_dec(v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref_known(v___x_1527_, 1);
lean_inc(v_a_1523_);
v___x_1528_ = l_Lean_Linter_List_bitVecWidths(v_a_1523_);
v___x_1529_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1528_, v___x_1522_, v___y_1517_, v___y_1518_);
lean_dec(v___x_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref_known(v___x_1529_, 1);
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1515_, v___x_1531_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1513_, v_sz_1514_, v___x_1532_, v___x_1530_, v___y_1517_, v___y_1518_);
return v___x_1533_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1529_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1529_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1527_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1527_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1525_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1525_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1513_ = stack[0].m_obj;
size_t v_sz_1514_ = stack[1].m_num;
size_t v_i_1515_ = stack[2].m_num;
lean_object* v_b_1516_ = stack[3].m_obj;
lean_object* v___y_1517_ = stack[4].m_obj;
lean_object* v___y_1518_ = stack[5].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_1513_, v_sz_1514_, v_i_1515_, v_b_1516_, v___y_1517_, v___y_1518_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
size_t v_sz_boxed_1566_; size_t v_i_boxed_1567_; lean_object* v_res_1568_; 
v_sz_boxed_1566_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1567_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_1559_, v_sz_boxed_1566_, v_i_boxed_1567_, v_b_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_as_1559_);
return v_res_1568_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(lean_object* v_t_1569_, lean_object* v_init_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_root_1574_; lean_object* v_tail_1575_; lean_object* v___x_1576_; 
v_root_1574_ = lean_ctor_get(v_t_1569_, 0);
v_tail_1575_ = lean_ctor_get(v_t_1569_, 1);
v___x_1576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1570_, v_root_1574_, v_init_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1613_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1613_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1613_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
if (lean_obj_tag(v_a_1577_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; 
v_a_1581_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v_a_1577_, 1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_a_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1581_);
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
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1579_);
v_a_1585_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v_a_1577_, 1);
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_a_1585_);
v_sz_1588_ = lean_array_size(v_tail_1575_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_1575_, v_sz_1588_, v___x_1589_, v___x_1587_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1604_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_fst_1595_; 
v_fst_1595_ = lean_ctor_get(v_a_1591_, 0);
if (lean_obj_tag(v_fst_1595_) == 0)
{
lean_object* v_snd_1596_; lean_object* v___x_1598_; 
v_snd_1596_ = lean_ctor_get(v_a_1591_, 1);
lean_inc(v_snd_1596_);
lean_dec(v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_snd_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_snd_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
lean_inc_ref(v_fst_1595_);
lean_dec(v_a_1591_);
v_val_1600_ = lean_ctor_get(v_fst_1595_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_fst_1595_, 1);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_val_1600_);
v___x_1602_ = v___x_1593_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1590_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1590_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1576_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1576_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1569_ = stack[0].m_obj;
lean_object* v_init_1570_ = stack[1].m_obj;
lean_object* v___y_1571_ = stack[2].m_obj;
lean_object* v___y_1572_ = stack[3].m_obj;
lean_object* v_res_1622_;
v_res_1622_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_t_1569_, v_init_1570_, v___y_1571_, v___y_1572_);
stack->m_obj
 = v_res_1622_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(lean_object* v_t_1623_, lean_object* v_init_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_t_1623_, v_init_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_t_1623_);
return v_res_1628_;
}
}
lean_object* l_Lean_Linter_List_indexLinter___lam__0(lean_object* v_stx_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_scopes_1638_; lean_object* v___x_1639_; lean_object* v_opts_1640_; lean_object* v___x_1641_; lean_object* v_name_1642_; lean_object* v_map_1643_; lean_object* v___x_1644_; 
v___x_1633_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1634_ = lean_st_ref_get(v___y_1631_);
v_scopes_1638_ = lean_ctor_get(v___x_1634_, 2);
lean_inc(v_scopes_1638_);
lean_dec(v___x_1634_);
v___x_1639_ = l_List_head_x21___redArg(v___x_1633_, v_scopes_1638_);
lean_dec(v_scopes_1638_);
v_opts_1640_ = lean_ctor_get(v___x_1639_, 1);
lean_inc_ref(v_opts_1640_);
lean_dec(v___x_1639_);
v___x_1641_ = l_Lean_Linter_List_linter_indexVariables;
v_name_1642_ = lean_ctor_get(v___x_1641_, 0);
v_map_1643_ = lean_ctor_get(v_opts_1640_, 0);
lean_inc(v_map_1643_);
lean_dec_ref(v_opts_1640_);
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1643_, v_name_1642_);
lean_dec(v_map_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
goto v___jp_1635_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1677_; 
v_val_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1677_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_val_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1677_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
if (lean_obj_tag(v_val_1645_) == 1)
{
uint8_t v_v_1649_; 
v_v_1649_ = lean_ctor_get_uint8(v_val_1645_, 0);
lean_dec_ref_known(v_val_1645_, 0);
if (v_v_1649_ == 0)
{
lean_del_object(v___x_1647_);
goto v___jp_1635_;
}
else
{
lean_object* v___x_1650_; lean_object* v_messages_1651_; uint8_t v___x_1652_; 
v___x_1650_ = lean_st_ref_get(v___y_1631_);
v_messages_1651_ = lean_ctor_get(v___x_1650_, 1);
lean_inc_ref(v_messages_1651_);
lean_dec(v___x_1650_);
v___x_1652_ = l_Lean_MessageLog_hasErrors(v_messages_1651_);
lean_dec_ref(v_messages_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v_infoState_1659_; uint8_t v_enabled_1660_; 
v___x_1653_ = lean_st_ref_get(v___y_1631_);
v_infoState_1659_ = lean_ctor_get(v___x_1653_, 8);
lean_inc_ref(v_infoState_1659_);
lean_dec(v___x_1653_);
v_enabled_1660_ = lean_ctor_get_uint8(v_infoState_1659_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1659_);
if (v_enabled_1660_ == 0)
{
goto v___jp_1654_;
}
else
{
if (v___x_1652_ == 0)
{
lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_del_object(v___x_1647_);
v___x_1661_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_1631_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = lean_box(0);
v___x_1664_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_1662_, v___x_1663_, v___y_1630_, v___y_1631_);
lean_dec(v_a_1662_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v___x_1664_, 0);
lean_dec(v_unused_1672_);
v___x_1666_ = v___x_1664_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v___x_1664_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1663_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1663_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
return v___x_1664_;
}
}
else
{
goto v___jp_1654_;
}
}
v___jp_1654_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_box(0);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1655_);
v___x_1657_ = v___x_1647_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_box(0);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1673_);
v___x_1675_ = v___x_1647_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_del_object(v___x_1647_);
lean_dec(v_val_1645_);
goto v___jp_1635_;
}
}
}
v___jp_1635_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_List_indexLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1629_ = stack[0].m_obj;
lean_object* v___y_1630_ = stack[1].m_obj;
lean_object* v___y_1631_ = stack[2].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_1629_, v___y_1630_, v___y_1631_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0___boxed(lean_object* v_stx_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_stx_1679_);
return v_res_1683_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(lean_object* v_as_1697_, lean_object* v_as_x27_1698_, lean_object* v_b_1699_, lean_object* v_a_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1698_, v_b_1699_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1697_ = stack[0].m_obj;
lean_object* v_as_x27_1698_ = stack[1].m_obj;
lean_object* v_b_1699_ = stack[2].m_obj;
lean_object* v___y_1701_ = stack[4].m_obj;
lean_object* v___y_1702_ = stack[5].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(v_as_1697_, v_as_x27_1698_, v_b_1699_, lean_box(0), v___y_1701_, v___y_1702_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(lean_object* v_as_1706_, lean_object* v_as_x27_1707_, lean_object* v_b_1708_, lean_object* v_a_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(v_as_1706_, v_as_x27_1707_, v_b_1708_, v_a_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_as_x27_1707_);
lean_dec(v_as_1706_);
return v_res_1713_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(lean_object* v_as_1714_, lean_object* v_as_x27_1715_, lean_object* v_b_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1715_, v_b_1716_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1714_ = stack[0].m_obj;
lean_object* v_as_x27_1715_ = stack[1].m_obj;
lean_object* v_b_1716_ = stack[2].m_obj;
lean_object* v___y_1718_ = stack[4].m_obj;
lean_object* v___y_1719_ = stack[5].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(v_as_1714_, v_as_x27_1715_, v_b_1716_, lean_box(0), v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(lean_object* v_as_1723_, lean_object* v_as_x27_1724_, lean_object* v_b_1725_, lean_object* v_a_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(v_as_1723_, v_as_x27_1724_, v_b_1725_, v_a_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v_as_x27_1724_);
lean_dec(v_as_1723_);
return v_res_1730_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(lean_object* v_as_1731_, lean_object* v_as_x27_1732_, lean_object* v_b_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1732_, v_b_1733_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1731_ = stack[0].m_obj;
lean_object* v_as_x27_1732_ = stack[1].m_obj;
lean_object* v_b_1733_ = stack[2].m_obj;
lean_object* v___y_1735_ = stack[4].m_obj;
lean_object* v___y_1736_ = stack[5].m_obj;
lean_object* v_res_1739_;
v_res_1739_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(v_as_1731_, v_as_x27_1732_, v_b_1733_, lean_box(0), v___y_1735_, v___y_1736_);
stack->m_obj
 = v_res_1739_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(lean_object* v_as_1740_, lean_object* v_as_x27_1741_, lean_object* v_b_1742_, lean_object* v_a_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(v_as_1740_, v_as_x27_1741_, v_b_1742_, v_a_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v_as_x27_1741_);
lean_dec(v_as_1740_);
return v_res_1747_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(lean_object* v_msgData_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_1748_, v___y_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1748_ = stack[0].m_obj;
lean_object* v___y_1749_ = stack[1].m_obj;
lean_object* v___y_1750_ = stack[2].m_obj;
lean_object* v_res_1753_;
v_res_1753_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_1748_, v___y_1749_, v___y_1750_);
stack->m_obj
 = v_res_1753_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_msgData_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1758_;
}
}
lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_Linter_List_indexLinter));
v___x_1761_ = l_Lean_Elab_Command_addLinter(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1762_;
v_res_1762_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1762_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
return v_res_1764_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(lean_object* v_e_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Lean_Expr_hasMVar(v_e_1823_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_e_1823_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v_mctx_1829_; lean_object* v___x_1830_; lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v___x_1833_; lean_object* v_cache_1834_; lean_object* v_zetaDeltaFVarIds_1835_; lean_object* v_postponed_1836_; lean_object* v_diag_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1846_; 
v___x_1828_ = lean_st_ref_get(v___y_1824_);
v_mctx_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_ref(v_mctx_1829_);
lean_dec(v___x_1828_);
v___x_1830_ = l_Lean_instantiateMVarsCore(v_mctx_1829_, v_e_1823_);
v_fst_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_fst_1831_);
v_snd_1832_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v___x_1830_);
v___x_1833_ = lean_st_ref_take(v___y_1824_);
v_cache_1834_ = lean_ctor_get(v___x_1833_, 1);
v_zetaDeltaFVarIds_1835_ = lean_ctor_get(v___x_1833_, 2);
v_postponed_1836_ = lean_ctor_get(v___x_1833_, 3);
v_diag_1837_ = lean_ctor_get(v___x_1833_, 4);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1833_, 0);
lean_dec(v_unused_1847_);
v___x_1839_ = v___x_1833_;
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_diag_1837_);
lean_inc(v_postponed_1836_);
lean_inc(v_zetaDeltaFVarIds_1835_);
lean_inc(v_cache_1834_);
lean_dec(v___x_1833_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_snd_1832_);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_snd_1832_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_cache_1834_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_zetaDeltaFVarIds_1835_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_postponed_1836_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_diag_1837_);
v___x_1842_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_st_ref_put(v___y_1824_, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_fst_1831_);
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1823_ = stack[0].m_obj;
lean_object* v___y_1824_ = stack[1].m_obj;
lean_object* v_res_1848_;
v_res_1848_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1823_, v___y_1824_);
stack->m_obj
 = v_res_1848_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(lean_object* v_e_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1849_, v___y_1850_);
lean_dec(v___y_1850_);
return v_res_1852_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(lean_object* v_e_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1853_, v___y_1855_);
return v___x_1859_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1853_ = stack[0].m_obj;
lean_object* v___y_1854_ = stack[1].m_obj;
lean_object* v___y_1855_ = stack[2].m_obj;
lean_object* v___y_1856_ = stack[3].m_obj;
lean_object* v___y_1857_ = stack[4].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(v_e_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(lean_object* v_e_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(v_e_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1867_;
}
}
static lean_object* _init_l_Lean_Linter_List_binders___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = ((lean_object*)(l_Lean_Linter_List_binders___lam__0___closed__1));
v___x_1873_ = l_Lean_Expr_const___override(v___x_1872_, v___x_1871_);
return v___x_1873_;
}
}
lean_object* l_Lean_Linter_List_binders___lam__0(lean_object* v_expr_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___y_1881_; lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Meta_saveState___redArg(v___y_1876_, v___y_1878_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
lean_inc(v___y_1878_);
lean_inc(v___y_1876_);
v___x_1886_ = lean_infer_type(v_expr_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec(v_a_1885_);
lean_dec(v___y_1878_);
v___y_1881_ = v___x_1886_;
goto v___jp_1880_;
}
else
{
lean_object* v_a_1887_; uint8_t v___y_1889_; uint8_t v___x_1901_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v___x_1901_ = l_Lean_Exception_isInterrupt(v_a_1887_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; 
lean_inc(v_a_1887_);
v___x_1902_ = l_Lean_Exception_isRuntime(v_a_1887_);
v___y_1889_ = v___x_1902_;
goto v___jp_1888_;
}
else
{
v___y_1889_ = v___x_1901_;
goto v___jp_1888_;
}
v___jp_1888_:
{
if (v___y_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec_ref_known(v___x_1886_, 1);
v___x_1890_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1885_, v___y_1876_, v___y_1878_);
lean_dec(v___y_1878_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec_ref_known(v___x_1890_, 1);
v___x_1891_ = lean_obj_once(&l_Lean_Linter_List_binders___lam__0___closed__2, &l_Lean_Linter_List_binders___lam__0___closed__2_once, _init_l_Lean_Linter_List_binders___lam__0___closed__2);
v___x_1892_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_1891_, v___y_1876_);
lean_dec(v___y_1876_);
return v___x_1892_;
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v___y_1876_);
v_a_1893_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1890_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1890_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_dec(v_a_1885_);
lean_dec(v___y_1878_);
v___y_1881_ = v___x_1886_;
goto v___jp_1880_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v_expr_1874_);
v_a_1903_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1884_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1884_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
v___jp_1880_:
{
if (lean_obj_tag(v___y_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___y_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___y_1881_, 1);
v___x_1883_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_a_1882_, v___y_1876_);
lean_dec(v___y_1876_);
return v___x_1883_;
}
else
{
lean_dec(v___y_1876_);
return v___y_1881_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_List_binders___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_1874_ = stack[0].m_obj;
lean_object* v___y_1875_ = stack[1].m_obj;
lean_object* v___y_1876_ = stack[2].m_obj;
lean_object* v___y_1877_ = stack[3].m_obj;
lean_object* v___y_1878_ = stack[4].m_obj;
lean_object* v_res_1911_;
v_res_1911_ = l_Lean_Linter_List_binders___lam__0(v_expr_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1911_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0___boxed(lean_object* v_expr_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Linter_List_binders___lam__0(v_expr_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v_res_1918_;
}
}
lean_object* l_Lean_Linter_List_binders___lam__1(lean_object* v_p_1919_, lean_object* v_ctx_1920_, lean_object* v_ti_1921_){
_start:
{
uint8_t v_isBinder_1923_; 
v_isBinder_1923_ = lean_ctor_get_uint8(v_ti_1921_, sizeof(void*)*4);
if (v_isBinder_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v_ti_1921_);
lean_dec_ref(v_ctx_1920_);
lean_dec_ref(v_p_1919_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
else
{
lean_object* v_toElabInfo_1926_; lean_object* v_lctx_1927_; lean_object* v_expr_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v_toElabInfo_1926_ = lean_ctor_get(v_ti_1921_, 0);
lean_inc_ref(v_toElabInfo_1926_);
v_lctx_1927_ = lean_ctor_get(v_ti_1921_, 1);
lean_inc_ref_n(v_lctx_1927_, 2);
v_expr_1928_ = lean_ctor_get(v_ti_1921_, 3);
lean_inc_ref_n(v_expr_1928_, 2);
lean_dec_ref(v_ti_1921_);
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1929_, 0, v_expr_1928_);
v___x_1930_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1920_, v_lctx_1927_, v___f_1929_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1974_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1974_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1974_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
lean_inc(v_a_1931_);
v___x_1935_ = l_Lean_Expr_cleanupAnnotations(v_a_1931_);
v___x_1936_ = lean_apply_1(v_p_1919_, v___x_1935_);
v___x_1937_ = lean_unbox(v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v_a_1931_);
lean_dec_ref(v_expr_1928_);
lean_dec_ref(v_lctx_1927_);
lean_dec_ref(v_toElabInfo_1926_);
v___x_1938_ = lean_box(0);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1938_);
v___x_1940_ = v___x_1933_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
else
{
if (lean_obj_tag(v_expr_1928_) == 1)
{
lean_object* v_fvarId_1942_; lean_object* v___x_1943_; 
v_fvarId_1942_ = lean_ctor_get(v_expr_1928_, 0);
lean_inc(v_fvarId_1942_);
lean_dec_ref_known(v_expr_1928_, 1);
v___x_1943_ = lean_local_ctx_find(v_lctx_1927_, v_fvarId_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec(v_a_1931_);
lean_dec_ref(v_toElabInfo_1926_);
v___x_1944_ = lean_box(0);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1944_);
v___x_1946_ = v___x_1933_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
else
{
lean_object* v_val_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1969_; 
v_val_1948_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1950_ = v___x_1943_;
v_isShared_1951_ = v_isSharedCheck_1969_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_val_1948_);
lean_dec(v___x_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1969_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_stx_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1967_; 
v_stx_1952_ = lean_ctor_get(v_toElabInfo_1926_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_toElabInfo_1926_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_toElabInfo_1926_, 0);
lean_dec(v_unused_1968_);
v___x_1954_ = v_toElabInfo_1926_;
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_stx_1952_);
lean_dec(v_toElabInfo_1926_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_LocalDecl_userName(v_val_1948_);
lean_dec(v_val_1948_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_a_1931_);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1931_);
v___x_1958_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_stx_1952_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1959_);
v___x_1961_ = v___x_1950_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1961_);
v___x_1963_ = v___x_1933_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec(v_a_1931_);
lean_dec_ref(v_expr_1928_);
lean_dec_ref(v_lctx_1927_);
lean_dec_ref(v_toElabInfo_1926_);
v___x_1970_ = lean_box(0);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1970_);
v___x_1972_ = v___x_1933_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_expr_1928_);
lean_dec_ref(v_lctx_1927_);
lean_dec_ref(v_toElabInfo_1926_);
lean_dec_ref(v_p_1919_);
v_a_1975_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1930_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1930_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_List_binders___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1919_ = stack[0].m_obj;
lean_object* v_ctx_1920_ = stack[1].m_obj;
lean_object* v_ti_1921_ = stack[2].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l_Lean_Linter_List_binders___lam__1(v_p_1919_, v_ctx_1920_, v_ti_1921_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1___boxed(lean_object* v_p_1984_, lean_object* v_ctx_1985_, lean_object* v_ti_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Linter_List_binders___lam__1(v_p_1984_, v_ctx_1985_, v_ti_1986_);
return v_res_1988_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1989_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1990_, lean_object* v___x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_object* v_cs_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2008_; 
v_cs_1995_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1997_ = v_x_1992_;
v_isShared_1998_ = v_isSharedCheck_2008_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_cs_1995_);
lean_dec(v_x_1992_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2008_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_array_get_size(v_cs_1995_);
v___x_2001_ = lean_nat_dec_lt(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v_cs_1995_);
lean_dec(v___x_1991_);
lean_dec_ref(v_f_1990_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v_x_1993_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_x_1993_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
else
{
size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
lean_del_object(v___x_1997_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = lean_usize_of_nat(v___x_2000_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_1990_, v___x_1991_, v_cs_1995_, v___x_2005_, v___x_2006_, v_x_1993_);
lean_dec_ref(v_cs_1995_);
return v___x_2007_;
}
}
}
else
{
lean_object* v_vs_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2022_; 
v_vs_2009_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2011_ = v_x_1992_;
v_isShared_2012_ = v_isSharedCheck_2022_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_vs_2009_);
lean_dec(v_x_1992_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2022_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_array_get_size(v_vs_2009_);
v___x_2015_ = lean_nat_dec_lt(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2017_; 
lean_dec_ref(v_vs_2009_);
lean_dec(v___x_1991_);
lean_dec_ref(v_f_1990_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 0);
lean_ctor_set(v___x_2011_, 0, v_x_1993_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_x_1993_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
size_t v___x_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
lean_del_object(v___x_2011_);
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = lean_usize_of_nat(v___x_2014_);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1990_, v___x_1991_, v_vs_2009_, v___x_2019_, v___x_2020_, v_x_1993_);
lean_dec_ref(v_vs_2009_);
return v___x_2021_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1990_ = stack[0].m_obj;
lean_object* v___x_1991_ = stack[1].m_obj;
lean_object* v_x_1992_ = stack[2].m_obj;
lean_object* v_x_1993_ = stack[3].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1990_, v___x_1991_, v_x_1992_, v_x_1993_);
stack->m_obj
 = v_res_2023_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_f_2024_, lean_object* v___x_2025_, lean_object* v_as_2026_, size_t v_i_2027_, size_t v_stop_2028_, lean_object* v_b_2029_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_eq(v_i_2027_, v_stop_2028_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_array_uget_borrowed(v_as_2026_, v_i_2027_);
lean_inc(v___x_2032_);
lean_inc(v___x_2025_);
lean_inc_ref(v_f_2024_);
v___x_2033_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2024_, v___x_2025_, v___x_2032_, v_b_2029_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; size_t v___x_2035_; size_t v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2027_, v___x_2035_);
v_i_2027_ = v___x_2036_;
v_b_2029_ = v_a_2034_;
goto _start;
}
else
{
lean_dec(v___x_2025_);
lean_dec_ref(v_f_2024_);
return v___x_2033_;
}
}
else
{
lean_object* v___x_2038_; 
lean_dec(v___x_2025_);
lean_dec_ref(v_f_2024_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_b_2029_);
return v___x_2038_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2024_ = stack[0].m_obj;
lean_object* v___x_2025_ = stack[1].m_obj;
lean_object* v_as_2026_ = stack[2].m_obj;
size_t v_i_2027_ = stack[3].m_num;
size_t v_stop_2028_ = stack[4].m_num;
lean_object* v_b_2029_ = stack[5].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2024_, v___x_2025_, v_as_2026_, v_i_2027_, v_stop_2028_, v_b_2029_);
stack->m_obj
 = v_res_2039_;
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_f_2040_, lean_object* v___x_2041_, lean_object* v_x_2042_, size_t v_x_2043_, size_t v_x_2044_, lean_object* v_x_2045_){
_start:
{
if (lean_obj_tag(v_x_2042_) == 0)
{
lean_object* v_cs_2047_; lean_object* v___x_2048_; size_t v___x_2049_; lean_object* v_j_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_cs_2047_ = lean_ctor_get(v_x_2042_, 0);
lean_inc_ref(v_cs_2047_);
lean_dec_ref_known(v_x_2042_, 1);
v___x_2048_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2049_ = lean_usize_shift_right(v_x_2043_, v_x_2044_);
v_j_2050_ = lean_usize_to_nat(v___x_2049_);
v___x_2051_ = lean_array_get_borrowed(v___x_2048_, v_cs_2047_, v_j_2050_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_shift_left(v___x_2052_, v_x_2044_);
v___x_2054_ = lean_usize_sub(v___x_2053_, v___x_2052_);
v___x_2055_ = lean_usize_land(v_x_2043_, v___x_2054_);
v___x_2056_ = ((size_t)5ULL);
v___x_2057_ = lean_usize_sub(v_x_2044_, v___x_2056_);
lean_inc(v___x_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v_f_2040_);
v___x_2058_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2040_, v___x_2041_, v___x_2051_, v___x_2055_, v___x_2057_, v_x_2045_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_add(v_j_2050_, v___x_2060_);
lean_dec(v_j_2050_);
v___x_2062_ = lean_array_get_size(v_cs_2047_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec(v___x_2061_);
lean_dec_ref(v_cs_2047_);
lean_dec(v___x_2041_);
lean_dec_ref(v_f_2040_);
return v___x_2058_;
}
else
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2064_ = lean_usize_of_nat(v___x_2061_);
lean_dec(v___x_2061_);
v___x_2065_ = lean_usize_of_nat(v___x_2062_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2040_, v___x_2041_, v_cs_2047_, v___x_2064_, v___x_2065_, v_a_2059_);
lean_dec_ref(v_cs_2047_);
return v___x_2066_;
}
}
else
{
lean_dec(v_j_2050_);
lean_dec_ref(v_cs_2047_);
lean_dec(v___x_2041_);
lean_dec_ref(v_f_2040_);
return v___x_2058_;
}
}
else
{
lean_object* v_vs_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2080_; 
v_vs_2067_ = lean_ctor_get(v_x_2042_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_x_2042_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2069_ = v_x_2042_;
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_vs_2067_);
lean_dec(v_x_2042_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2071_ = lean_usize_to_nat(v_x_2043_);
v___x_2072_ = lean_array_get_size(v_vs_2067_);
v___x_2073_ = lean_nat_dec_lt(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2075_; 
lean_dec(v___x_2071_);
lean_dec_ref(v_vs_2067_);
lean_dec(v___x_2041_);
lean_dec_ref(v_f_2040_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 0);
lean_ctor_set(v___x_2069_, 0, v_x_2045_);
v___x_2075_ = v___x_2069_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_x_2045_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
else
{
size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
lean_del_object(v___x_2069_);
v___x_2077_ = lean_usize_of_nat(v___x_2071_);
lean_dec(v___x_2071_);
v___x_2078_ = lean_usize_of_nat(v___x_2072_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2040_, v___x_2041_, v_vs_2067_, v___x_2077_, v___x_2078_, v_x_2045_);
lean_dec_ref(v_vs_2067_);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2040_ = stack[0].m_obj;
lean_object* v___x_2041_ = stack[1].m_obj;
lean_object* v_x_2042_ = stack[2].m_obj;
size_t v_x_2043_ = stack[3].m_num;
size_t v_x_2044_ = stack[4].m_num;
lean_object* v_x_2045_ = stack[5].m_obj;
lean_object* v_res_2081_;
v_res_2081_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2040_, v___x_2041_, v_x_2042_, v_x_2043_, v_x_2044_, v_x_2045_);
stack->m_obj
 = v_res_2081_;
}
lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_2082_, lean_object* v___x_2083_, lean_object* v_t_2084_, lean_object* v_init_2085_, lean_object* v_start_2086_){
_start:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_nat_dec_eq(v_start_2086_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v_root_2090_; lean_object* v_tail_2091_; size_t v_shift_2092_; lean_object* v_tailOff_2093_; uint8_t v___x_2094_; 
v_root_2090_ = lean_ctor_get(v_t_2084_, 0);
lean_inc_ref(v_root_2090_);
v_tail_2091_ = lean_ctor_get(v_t_2084_, 1);
lean_inc_ref(v_tail_2091_);
v_shift_2092_ = lean_ctor_get_usize(v_t_2084_, 4);
v_tailOff_2093_ = lean_ctor_get(v_t_2084_, 3);
lean_inc(v_tailOff_2093_);
lean_dec_ref(v_t_2084_);
v___x_2094_ = lean_nat_dec_le(v_tailOff_2093_, v_start_2086_);
if (v___x_2094_ == 0)
{
size_t v___x_2095_; lean_object* v___x_2096_; 
lean_dec(v_tailOff_2093_);
v___x_2095_ = lean_usize_of_nat(v_start_2086_);
lean_inc(v___x_2083_);
lean_inc_ref(v_f_2082_);
v___x_2096_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2082_, v___x_2083_, v_root_2090_, v___x_2095_, v_shift_2092_, v_init_2085_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v___x_2098_ = lean_array_get_size(v_tail_2091_);
v___x_2099_ = lean_nat_dec_lt(v___x_2088_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v_tail_2091_);
lean_dec(v___x_2083_);
lean_dec_ref(v_f_2082_);
return v___x_2096_;
}
else
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = lean_usize_of_nat(v___x_2098_);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2082_, v___x_2083_, v_tail_2091_, v___x_2100_, v___x_2101_, v_a_2097_);
lean_dec_ref(v_tail_2091_);
return v___x_2102_;
}
}
else
{
lean_dec_ref(v_tail_2091_);
lean_dec(v___x_2083_);
lean_dec_ref(v_f_2082_);
return v___x_2096_;
}
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_dec_ref(v_root_2090_);
v___x_2103_ = lean_nat_sub(v_start_2086_, v_tailOff_2093_);
lean_dec(v_tailOff_2093_);
v___x_2104_ = lean_array_get_size(v_tail_2091_);
v___x_2105_ = lean_nat_dec_lt(v___x_2103_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec(v___x_2103_);
lean_dec_ref(v_tail_2091_);
lean_dec(v___x_2083_);
lean_dec_ref(v_f_2082_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_init_2085_);
return v___x_2106_;
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_usize_of_nat(v___x_2103_);
lean_dec(v___x_2103_);
v___x_2108_ = lean_usize_of_nat(v___x_2104_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2082_, v___x_2083_, v_tail_2091_, v___x_2107_, v___x_2108_, v_init_2085_);
lean_dec_ref(v_tail_2091_);
return v___x_2109_;
}
}
}
else
{
lean_object* v_root_2110_; lean_object* v_tail_2111_; lean_object* v___x_2112_; 
v_root_2110_ = lean_ctor_get(v_t_2084_, 0);
lean_inc_ref(v_root_2110_);
v_tail_2111_ = lean_ctor_get(v_t_2084_, 1);
lean_inc_ref(v_tail_2111_);
lean_dec_ref(v_t_2084_);
lean_inc(v___x_2083_);
lean_inc_ref(v_f_2082_);
v___x_2112_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2082_, v___x_2083_, v_root_2110_, v_init_2085_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v___x_2114_ = lean_array_get_size(v_tail_2111_);
v___x_2115_ = lean_nat_dec_lt(v___x_2088_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec_ref(v_tail_2111_);
lean_dec(v___x_2083_);
lean_dec_ref(v_f_2082_);
return v___x_2112_;
}
else
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = lean_usize_of_nat(v___x_2114_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2082_, v___x_2083_, v_tail_2111_, v___x_2116_, v___x_2117_, v_a_2113_);
lean_dec_ref(v_tail_2111_);
return v___x_2118_;
}
}
else
{
lean_dec_ref(v_tail_2111_);
lean_dec(v___x_2083_);
lean_dec_ref(v_f_2082_);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2082_ = stack[0].m_obj;
lean_object* v___x_2083_ = stack[1].m_obj;
lean_object* v_t_2084_ = stack[2].m_obj;
lean_object* v_init_2085_ = stack[3].m_obj;
lean_object* v_start_2086_ = stack[4].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2082_, v___x_2083_, v_t_2084_, v_init_2085_, v_start_2086_);
stack->m_obj
 = v_res_2119_;
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2120_, lean_object* v_ctx_x3f_2121_, lean_object* v_a_2122_, lean_object* v_x_2123_){
_start:
{
switch(lean_obj_tag(v_x_2123_))
{
case 0:
{
lean_object* v_i_2125_; lean_object* v_t_2126_; lean_object* v___x_2127_; 
v_i_2125_ = lean_ctor_get(v_x_2123_, 0);
lean_inc_ref(v_i_2125_);
v_t_2126_ = lean_ctor_get(v_x_2123_, 1);
lean_inc_ref(v_t_2126_);
lean_dec_ref_known(v_x_2123_, 2);
v___x_2127_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2125_, v_ctx_x3f_2121_);
v_ctx_x3f_2121_ = v___x_2127_;
v_x_2123_ = v_t_2126_;
goto _start;
}
case 1:
{
lean_object* v_i_2129_; lean_object* v_children_2130_; lean_object* v_a_2132_; 
v_i_2129_ = lean_ctor_get(v_x_2123_, 0);
lean_inc_ref(v_i_2129_);
v_children_2130_ = lean_ctor_get(v_x_2123_, 1);
lean_inc_ref(v_children_2130_);
lean_dec_ref_known(v_x_2123_, 2);
if (lean_obj_tag(v_ctx_x3f_2121_) == 0)
{
v_a_2132_ = v_a_2122_;
goto v___jp_2131_;
}
else
{
lean_object* v_val_2136_; lean_object* v___x_2137_; 
v_val_2136_ = lean_ctor_get(v_ctx_x3f_2121_, 0);
lean_inc_ref(v_f_2120_);
lean_inc_ref(v_i_2129_);
lean_inc(v_val_2136_);
v___x_2137_ = lean_apply_4(v_f_2120_, v_val_2136_, v_i_2129_, v_a_2122_, lean_box(0));
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_a_2132_ = v_a_2138_;
goto v___jp_2131_;
}
else
{
lean_dec_ref_known(v_ctx_x3f_2121_, 1);
lean_dec_ref(v_children_2130_);
lean_dec_ref(v_i_2129_);
lean_dec_ref(v_f_2120_);
return v___x_2137_;
}
}
v___jp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2121_, v_i_2129_);
lean_dec_ref(v_i_2129_);
v___x_2134_ = lean_unsigned_to_nat(0u);
v___x_2135_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2120_, v___x_2133_, v_children_2130_, v_a_2132_, v___x_2134_);
return v___x_2135_;
}
}
default: 
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_ctx_x3f_2121_);
lean_dec_ref(v_f_2120_);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_x_2123_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_x_2123_, 0);
lean_dec(v_unused_2146_);
v___x_2140_ = v_x_2123_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_x_2123_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2122_);
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2122_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2120_ = stack[0].m_obj;
lean_object* v_ctx_x3f_2121_ = stack[1].m_obj;
lean_object* v_a_2122_ = stack[2].m_obj;
lean_object* v_x_2123_ = stack[3].m_obj;
lean_object* v_res_2147_;
v_res_2147_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2120_, v_ctx_x3f_2121_, v_a_2122_, v_x_2123_);
stack->m_obj
 = v_res_2147_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2148_, lean_object* v___x_2149_, lean_object* v_as_2150_, size_t v_i_2151_, size_t v_stop_2152_, lean_object* v_b_2153_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_eq(v_i_2151_, v_stop_2152_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_array_uget_borrowed(v_as_2150_, v_i_2151_);
lean_inc(v___x_2156_);
lean_inc(v___x_2149_);
lean_inc_ref(v_f_2148_);
v___x_2157_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2148_, v___x_2149_, v_b_2153_, v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; size_t v___x_2159_; size_t v___x_2160_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2151_, v___x_2159_);
v_i_2151_ = v___x_2160_;
v_b_2153_ = v_a_2158_;
goto _start;
}
else
{
lean_dec(v___x_2149_);
lean_dec_ref(v_f_2148_);
return v___x_2157_;
}
}
else
{
lean_object* v___x_2162_; 
lean_dec(v___x_2149_);
lean_dec_ref(v_f_2148_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_b_2153_);
return v___x_2162_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2148_ = stack[0].m_obj;
lean_object* v___x_2149_ = stack[1].m_obj;
lean_object* v_as_2150_ = stack[2].m_obj;
size_t v_i_2151_ = stack[3].m_num;
size_t v_stop_2152_ = stack[4].m_num;
lean_object* v_b_2153_ = stack[5].m_obj;
lean_object* v_res_2163_;
v_res_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2148_, v___x_2149_, v_as_2150_, v_i_2151_, v_stop_2152_, v_b_2153_);
stack->m_obj
 = v_res_2163_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_2164_, lean_object* v___x_2165_, lean_object* v_as_2166_, lean_object* v_i_2167_, lean_object* v_stop_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_){
_start:
{
size_t v_i_boxed_2171_; size_t v_stop_boxed_2172_; lean_object* v_res_2173_; 
v_i_boxed_2171_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_stop_boxed_2172_ = lean_unbox_usize(v_stop_2168_);
lean_dec(v_stop_2168_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2164_, v___x_2165_, v_as_2166_, v_i_boxed_2171_, v_stop_boxed_2172_, v_b_2169_);
lean_dec_ref(v_as_2166_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_2174_, lean_object* v___x_2175_, lean_object* v_as_2176_, lean_object* v_i_2177_, lean_object* v_stop_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_){
_start:
{
size_t v_i_boxed_2181_; size_t v_stop_boxed_2182_; lean_object* v_res_2183_; 
v_i_boxed_2181_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_stop_boxed_2182_ = lean_unbox_usize(v_stop_2178_);
lean_dec(v_stop_2178_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2174_, v___x_2175_, v_as_2176_, v_i_boxed_2181_, v_stop_boxed_2182_, v_b_2179_);
lean_dec_ref(v_as_2176_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_2184_, lean_object* v_ctx_x3f_2185_, lean_object* v_a_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2184_, v_ctx_x3f_2185_, v_a_2186_, v_x_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_2190_, lean_object* v___x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2190_, v___x_2191_, v_x_2192_, v_x_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_f_2196_, lean_object* v___x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v___y_2202_){
_start:
{
size_t v_x_2637__boxed_2203_; size_t v_x_2638__boxed_2204_; lean_object* v_res_2205_; 
v_x_2637__boxed_2203_ = lean_unbox_usize(v_x_2199_);
lean_dec(v_x_2199_);
v_x_2638__boxed_2204_ = lean_unbox_usize(v_x_2200_);
lean_dec(v_x_2200_);
v_res_2205_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2196_, v___x_2197_, v_x_2198_, v_x_2637__boxed_2203_, v_x_2638__boxed_2204_, v_x_2201_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_2206_, lean_object* v___x_2207_, lean_object* v_t_2208_, lean_object* v_init_2209_, lean_object* v_start_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2206_, v___x_2207_, v_t_2208_, v_init_2209_, v_start_2210_);
lean_dec(v_start_2210_);
return v_res_2212_;
}
}
lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(lean_object* v_f_2213_, lean_object* v_init_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2213_, v___x_2217_, v_init_2214_, v_x_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2213_ = stack[0].m_obj;
lean_object* v_init_2214_ = stack[1].m_obj;
lean_object* v_x_2215_ = stack[2].m_obj;
lean_object* v_res_2219_;
v_res_2219_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2213_, v_init_2214_, v_x_2215_);
stack->m_obj
 = v_res_2219_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(lean_object* v_f_2220_, lean_object* v_init_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2220_, v_init_2221_, v_x_2222_);
return v_res_2224_;
}
}
lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(lean_object* v_f_2225_, lean_object* v_ctx_2226_, lean_object* v_info_2227_, lean_object* v_result_2228_){
_start:
{
if (lean_obj_tag(v_info_2227_) == 1)
{
lean_object* v_i_2230_; lean_object* v___x_2231_; 
v_i_2230_ = lean_ctor_get(v_info_2227_, 0);
lean_inc_ref(v_i_2230_);
lean_dec_ref_known(v_info_2227_, 1);
v___x_2231_ = lean_apply_3(v_f_2225_, v_ctx_2226_, v_i_2230_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2244_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
if (lean_obj_tag(v_a_2232_) == 0)
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_result_2228_);
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_result_2228_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
lean_object* v_val_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v_val_2239_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v_a_2232_, 1);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_val_2239_);
lean_ctor_set(v___x_2240_, 1, v_result_2228_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2240_);
v___x_2242_ = v___x_2234_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_result_2228_);
v_a_2245_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2231_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2231_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v___x_2253_; 
lean_dec_ref(v_info_2227_);
lean_dec_ref(v_ctx_2226_);
lean_dec_ref(v_f_2225_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_result_2228_);
return v___x_2253_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2225_ = stack[0].m_obj;
lean_object* v_ctx_2226_ = stack[1].m_obj;
lean_object* v_info_2227_ = stack[2].m_obj;
lean_object* v_result_2228_ = stack[3].m_obj;
lean_object* v_res_2254_;
v_res_2254_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_2225_, v_ctx_2226_, v_info_2227_, v_result_2228_);
stack->m_obj
 = v_res_2254_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(lean_object* v_f_2255_, lean_object* v_ctx_2256_, lean_object* v_info_2257_, lean_object* v_result_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_2255_, v_ctx_2256_, v_info_2257_, v_result_2258_);
return v_res_2260_;
}
}
lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(lean_object* v_t_2261_, lean_object* v_f_2262_){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2264_, 0, v_f_2262_);
v___x_2265_ = lean_box(0);
v___x_2266_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_2264_, v___x_2265_, v_t_2261_);
return v___x_2266_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2261_ = stack[0].m_obj;
lean_object* v_f_2262_ = stack[1].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2261_, v_f_2262_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(lean_object* v_t_2268_, lean_object* v_f_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2268_, v_f_2269_);
return v_res_2271_;
}
}
lean_object* l_Lean_Linter_List_binders(lean_object* v_t_2272_, lean_object* v_p_2273_){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2275_, 0, v_p_2273_);
v___x_2276_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2272_, v___f_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT void l_Lean_Linter_List_binders_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2272_ = stack[0].m_obj;
lean_object* v_p_2273_ = stack[1].m_obj;
lean_object* v_res_2277_;
v_res_2277_ = l_Lean_Linter_List_binders(v_t_2272_, v_p_2273_);
stack->m_obj
 = v_res_2277_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___boxed(lean_object* v_t_2278_, lean_object* v_p_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Linter_List_binders(v_t_2278_, v_p_2279_);
return v_res_2281_;
}
}
lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_object* v_00_u03b1_2282_, lean_object* v_t_2283_, lean_object* v_f_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2283_, v_f_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2283_ = stack[1].m_obj;
lean_object* v_f_2284_ = stack[2].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_box(0), v_t_2283_, v_f_2284_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_t_2289_, lean_object* v_f_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(v_00_u03b1_2288_, v_t_2289_, v_f_2290_);
return v_res_2292_;
}
}
lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_object* v_00_u03b1_2293_, lean_object* v_f_2294_, lean_object* v_init_2295_, lean_object* v_x_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2294_, v_init_2295_, v_x_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2294_ = stack[1].m_obj;
lean_object* v_init_2295_ = stack[2].m_obj;
lean_object* v_x_2296_ = stack[3].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_box(0), v_f_2294_, v_init_2295_, v_x_2296_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_f_2301_, lean_object* v_init_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_2300_, v_f_2301_, v_init_2302_, v_x_2303_);
return v_res_2305_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_2306_, lean_object* v_f_2307_, lean_object* v_ctx_x3f_2308_, lean_object* v_a_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2307_, v_ctx_x3f_2308_, v_a_2309_, v_x_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2307_ = stack[1].m_obj;
lean_object* v_ctx_x3f_2308_ = stack[2].m_obj;
lean_object* v_a_2309_ = stack[3].m_obj;
lean_object* v_x_2310_ = stack[4].m_obj;
lean_object* v_res_2313_;
v_res_2313_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_box(0), v_f_2307_, v_ctx_x3f_2308_, v_a_2309_, v_x_2310_);
stack->m_obj
 = v_res_2313_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2314_, lean_object* v_f_2315_, lean_object* v_ctx_x3f_2316_, lean_object* v_a_2317_, lean_object* v_x_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_2314_, v_f_2315_, v_ctx_x3f_2316_, v_a_2317_, v_x_2318_);
return v_res_2320_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2321_, lean_object* v_f_2322_, lean_object* v___x_2323_, lean_object* v_t_2324_, lean_object* v_init_2325_, lean_object* v_start_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2322_, v___x_2323_, v_t_2324_, v_init_2325_, v_start_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2322_ = stack[1].m_obj;
lean_object* v___x_2323_ = stack[2].m_obj;
lean_object* v_t_2324_ = stack[3].m_obj;
lean_object* v_init_2325_ = stack[4].m_obj;
lean_object* v_start_2326_ = stack[5].m_obj;
lean_object* v_res_2329_;
v_res_2329_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_box(0), v_f_2322_, v___x_2323_, v_t_2324_, v_init_2325_, v_start_2326_);
stack->m_obj
 = v_res_2329_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2330_, lean_object* v_f_2331_, lean_object* v___x_2332_, lean_object* v_t_2333_, lean_object* v_init_2334_, lean_object* v_start_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_2330_, v_f_2331_, v___x_2332_, v_t_2333_, v_init_2334_, v_start_2335_);
lean_dec(v_start_2335_);
return v_res_2337_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2338_, lean_object* v_f_2339_, lean_object* v___x_2340_, lean_object* v_x_2341_, size_t v_x_2342_, size_t v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2339_, v___x_2340_, v_x_2341_, v_x_2342_, v_x_2343_, v_x_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2339_ = stack[1].m_obj;
lean_object* v___x_2340_ = stack[2].m_obj;
lean_object* v_x_2341_ = stack[3].m_obj;
size_t v_x_2342_ = stack[4].m_num;
size_t v_x_2343_ = stack[5].m_num;
lean_object* v_x_2344_ = stack[6].m_obj;
lean_object* v_res_2347_;
v_res_2347_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_box(0), v_f_2339_, v___x_2340_, v_x_2341_, v_x_2342_, v_x_2343_, v_x_2344_);
stack->m_obj
 = v_res_2347_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_f_2349_, lean_object* v___x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v___y_2355_){
_start:
{
size_t v_x_3210__boxed_2356_; size_t v_x_3211__boxed_2357_; lean_object* v_res_2358_; 
v_x_3210__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_x_3211__boxed_2357_ = lean_unbox_usize(v_x_2353_);
lean_dec(v_x_2353_);
v_res_2358_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_2348_, v_f_2349_, v___x_2350_, v_x_2351_, v_x_3210__boxed_2356_, v_x_3211__boxed_2357_, v_x_2354_);
return v_res_2358_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2359_, lean_object* v_f_2360_, lean_object* v___x_2361_, lean_object* v_as_2362_, size_t v_i_2363_, size_t v_stop_2364_, lean_object* v_b_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2360_, v___x_2361_, v_as_2362_, v_i_2363_, v_stop_2364_, v_b_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2360_ = stack[1].m_obj;
lean_object* v___x_2361_ = stack[2].m_obj;
lean_object* v_as_2362_ = stack[3].m_obj;
size_t v_i_2363_ = stack[4].m_num;
size_t v_stop_2364_ = stack[5].m_num;
lean_object* v_b_2365_ = stack[6].m_obj;
lean_object* v_res_2368_;
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_box(0), v_f_2360_, v___x_2361_, v_as_2362_, v_i_2363_, v_stop_2364_, v_b_2365_);
stack->m_obj
 = v_res_2368_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_f_2370_, lean_object* v___x_2371_, lean_object* v_as_2372_, lean_object* v_i_2373_, lean_object* v_stop_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_){
_start:
{
size_t v_i_boxed_2377_; size_t v_stop_boxed_2378_; lean_object* v_res_2379_; 
v_i_boxed_2377_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_stop_boxed_2378_ = lean_unbox_usize(v_stop_2374_);
lean_dec(v_stop_2374_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2369_, v_f_2370_, v___x_2371_, v_as_2372_, v_i_boxed_2377_, v_stop_boxed_2378_, v_b_2375_);
lean_dec_ref(v_as_2372_);
return v_res_2379_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_2380_, lean_object* v_f_2381_, lean_object* v___x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2381_, v___x_2382_, v_x_2383_, v_x_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2381_ = stack[1].m_obj;
lean_object* v___x_2382_ = stack[2].m_obj;
lean_object* v_x_2383_ = stack[3].m_obj;
lean_object* v_x_2384_ = stack[4].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_box(0), v_f_2381_, v___x_2382_, v_x_2383_, v_x_2384_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_f_2389_, lean_object* v___x_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_2388_, v_f_2389_, v___x_2390_, v_x_2391_, v_x_2392_);
return v_res_2394_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_2395_, lean_object* v_f_2396_, lean_object* v___x_2397_, lean_object* v_as_2398_, size_t v_i_2399_, size_t v_stop_2400_, lean_object* v_b_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2396_, v___x_2397_, v_as_2398_, v_i_2399_, v_stop_2400_, v_b_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2396_ = stack[1].m_obj;
lean_object* v___x_2397_ = stack[2].m_obj;
lean_object* v_as_2398_ = stack[3].m_obj;
size_t v_i_2399_ = stack[4].m_num;
size_t v_stop_2400_ = stack[5].m_num;
lean_object* v_b_2401_ = stack[6].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_box(0), v_f_2396_, v___x_2397_, v_as_2398_, v_i_2399_, v_stop_2400_, v_b_2401_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_f_2406_, lean_object* v___x_2407_, lean_object* v_as_2408_, lean_object* v_i_2409_, lean_object* v_stop_2410_, lean_object* v_b_2411_, lean_object* v___y_2412_){
_start:
{
size_t v_i_boxed_2413_; size_t v_stop_boxed_2414_; lean_object* v_res_2415_; 
v_i_boxed_2413_ = lean_unbox_usize(v_i_2409_);
lean_dec(v_i_2409_);
v_stop_boxed_2414_ = lean_unbox_usize(v_stop_2410_);
lean_dec(v_stop_2410_);
v_res_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_2405_, v_f_2406_, v___x_2407_, v_as_2408_, v_i_boxed_2413_, v_stop_boxed_2414_, v_b_2411_);
lean_dec_ref(v_as_2408_);
return v_res_2415_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(lean_object* v_as_x27_2422_, lean_object* v_b_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
if (lean_obj_tag(v_as_x27_2422_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_b_2423_);
return v___x_2427_;
}
else
{
lean_object* v_head_2428_; lean_object* v_snd_2429_; lean_object* v_tail_2430_; lean_object* v_fst_2431_; lean_object* v_fst_2432_; lean_object* v_snd_2433_; lean_object* v___x_2434_; 
v_head_2428_ = lean_ctor_get(v_as_x27_2422_, 0);
v_snd_2429_ = lean_ctor_get(v_head_2428_, 1);
v_tail_2430_ = lean_ctor_get(v_as_x27_2422_, 1);
v_fst_2431_ = lean_ctor_get(v_head_2428_, 0);
v_fst_2432_ = lean_ctor_get(v_snd_2429_, 0);
v_snd_2433_ = lean_ctor_get(v_snd_2429_, 1);
v___x_2434_ = lean_box(0);
if (lean_obj_tag(v_fst_2432_) == 1)
{
lean_object* v_str_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v_str_2435_ = lean_ctor_get(v_fst_2432_, 1);
lean_inc_ref(v_str_2435_);
v___x_2436_ = l_Lean_Linter_List_stripBinderName(v_str_2435_);
v___x_2437_ = ((lean_object*)(l_Lean_Linter_List_allowedArrayNames));
v___x_2438_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2439_ = l_Lean_Linter_List_linter_listVariables;
v___x_2450_ = l_Lean_Expr_getAppNumArgs(v_snd_2433_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_sub(v___x_2450_, v___x_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = l_Lean_Expr_getRevArg_x21(v_snd_2433_, v___x_2452_);
v___x_2454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2455_ = l_Lean_Expr_isAppOf(v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2457_ = l_Lean_Expr_isAppOf(v___x_2453_, v___x_2456_);
lean_dec_ref(v___x_2453_);
if (v___x_2457_ == 0)
{
goto v___jp_2440_;
}
else
{
goto v___jp_2446_;
}
}
else
{
lean_dec_ref(v___x_2453_);
goto v___jp_2446_;
}
v___jp_2440_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
v___x_2442_ = l_Lean_stringToMessageData(v___x_2436_);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
lean_inc(v_fst_2431_);
v___x_2444_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2439_, v_fst_2431_, v___x_2443_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref_known(v___x_2444_, 1);
v_as_x27_2422_ = v_tail_2430_;
v_b_2423_ = v___x_2434_;
goto _start;
}
else
{
return v___x_2444_;
}
}
v___jp_2446_:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2448_ = lean_string_dec_eq(v___x_2436_, v___x_2447_);
if (v___x_2448_ == 0)
{
goto v___jp_2440_;
}
else
{
lean_dec_ref(v___x_2436_);
v_as_x27_2422_ = v_tail_2430_;
v_b_2423_ = v___x_2434_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2436_);
v_as_x27_2422_ = v_tail_2430_;
v_b_2423_ = v___x_2434_;
goto _start;
}
}
else
{
v_as_x27_2422_ = v_tail_2430_;
v_b_2423_ = v___x_2434_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2422_ = stack[0].m_obj;
lean_object* v_b_2423_ = stack[1].m_obj;
lean_object* v___y_2424_ = stack[2].m_obj;
lean_object* v___y_2425_ = stack[3].m_obj;
lean_object* v_res_2460_;
v_res_2460_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_2422_, v_b_2423_, v___y_2424_, v___y_2425_);
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(lean_object* v_as_x27_2461_, lean_object* v_b_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_2461_, v_b_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v_as_x27_2461_);
return v_res_2466_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0));
v___x_2469_ = l_Lean_stringToMessageData(v___x_2468_);
return v___x_2469_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(lean_object* v_as_x27_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
if (lean_obj_tag(v_as_x27_2473_) == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_b_2474_);
return v___x_2478_;
}
else
{
lean_object* v_head_2479_; lean_object* v_snd_2480_; lean_object* v_tail_2481_; lean_object* v_fst_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; 
v_head_2479_ = lean_ctor_get(v_as_x27_2473_, 0);
v_snd_2480_ = lean_ctor_get(v_head_2479_, 1);
v_tail_2481_ = lean_ctor_get(v_as_x27_2473_, 1);
v_fst_2482_ = lean_ctor_get(v_head_2479_, 0);
v_fst_2483_ = lean_ctor_get(v_snd_2480_, 0);
v_snd_2484_ = lean_ctor_get(v_snd_2480_, 1);
v___x_2485_ = lean_box(0);
if (lean_obj_tag(v_fst_2483_) == 1)
{
lean_object* v_str_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_str_2486_ = lean_ctor_get(v_fst_2483_, 1);
lean_inc_ref(v_str_2486_);
v___x_2487_ = l_Lean_Linter_List_stripBinderName(v_str_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_Linter_List_allowedListNames));
v___x_2489_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2487_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2490_ = l_Lean_Linter_List_linter_listVariables;
v___x_2504_ = l_Lean_Expr_getAppNumArgs(v_snd_2484_);
v___x_2505_ = lean_unsigned_to_nat(1u);
v___x_2506_ = lean_nat_sub(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = l_Lean_Expr_getRevArg_x21(v_snd_2484_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2509_ = l_Lean_Expr_isAppOf(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2511_ = l_Lean_Expr_isAppOf(v___x_2507_, v___x_2510_);
lean_dec_ref(v___x_2507_);
if (v___x_2511_ == 0)
{
goto v___jp_2491_;
}
else
{
goto v___jp_2497_;
}
}
else
{
lean_dec_ref(v___x_2507_);
goto v___jp_2497_;
}
v___jp_2491_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
v___x_2493_ = l_Lean_stringToMessageData(v___x_2487_);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
lean_inc(v_fst_2482_);
v___x_2495_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2490_, v_fst_2482_, v___x_2494_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_dec_ref_known(v___x_2495_, 1);
v_as_x27_2473_ = v_tail_2481_;
v_b_2474_ = v___x_2485_;
goto _start;
}
else
{
return v___x_2495_;
}
}
v___jp_2497_:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2));
v___x_2499_ = lean_string_dec_eq(v___x_2487_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2501_ = lean_string_dec_eq(v___x_2487_, v___x_2500_);
if (v___x_2501_ == 0)
{
goto v___jp_2491_;
}
else
{
lean_dec_ref(v___x_2487_);
v_as_x27_2473_ = v_tail_2481_;
v_b_2474_ = v___x_2485_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2487_);
v_as_x27_2473_ = v_tail_2481_;
v_b_2474_ = v___x_2485_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2487_);
v_as_x27_2473_ = v_tail_2481_;
v_b_2474_ = v___x_2485_;
goto _start;
}
}
else
{
v_as_x27_2473_ = v_tail_2481_;
v_b_2474_ = v___x_2485_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2473_ = stack[0].m_obj;
lean_object* v_b_2474_ = stack[1].m_obj;
lean_object* v___y_2475_ = stack[2].m_obj;
lean_object* v___y_2476_ = stack[3].m_obj;
lean_object* v_res_2514_;
v_res_2514_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_2473_, v_b_2474_, v___y_2475_, v___y_2476_);
stack->m_obj
 = v_res_2514_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(lean_object* v_as_x27_2515_, lean_object* v_b_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_2515_, v_b_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v_as_x27_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
if (lean_obj_tag(v_a_2521_) == 0)
{
lean_object* v___x_2523_; 
v___x_2523_ = l_List_reverse___redArg(v_a_2522_);
return v___x_2523_;
}
else
{
lean_object* v_head_2524_; lean_object* v_snd_2525_; lean_object* v_tail_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2538_; 
v_head_2524_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_head_2524_);
v_snd_2525_ = lean_ctor_get(v_head_2524_, 1);
v_tail_2526_ = lean_ctor_get(v_a_2521_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2521_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_a_2521_, 0);
lean_dec(v_unused_2539_);
v___x_2528_ = v_a_2521_;
v_isShared_2529_ = v_isSharedCheck_2538_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_tail_2526_);
lean_dec(v_a_2521_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2538_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_snd_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_snd_2530_ = lean_ctor_get(v_snd_2525_, 1);
v___x_2531_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2532_ = l_Lean_Expr_isAppOf(v_snd_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_del_object(v___x_2528_);
lean_dec(v_head_2524_);
v_a_2521_ = v_tail_2526_;
goto _start;
}
else
{
lean_object* v___x_2535_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v_a_2522_);
v___x_2535_ = v___x_2528_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_head_2524_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2522_);
v___x_2535_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
v_a_2521_ = v_tail_2526_;
v_a_2522_ = v___x_2535_;
goto _start;
}
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(uint8_t v_v_2540_, lean_object* v_x_2541_){
_start:
{
return v_v_2540_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_2540_ = stack[0].m_num;
lean_object* v_x_2541_ = stack[1].m_obj;
uint8_t v_res_2542_;
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v_v_2540_, v_x_2541_);
stack->m_num = v_res_2542_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(lean_object* v_v_2543_, lean_object* v_x_2544_){
_start:
{
uint8_t v_v_13054__boxed_2545_; uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_v_13054__boxed_2545_ = lean_unbox(v_v_2543_);
v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v_v_13054__boxed_2545_, v_x_2544_);
lean_dec_ref(v_x_2544_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
if (lean_obj_tag(v_a_2548_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = l_List_reverse___redArg(v_a_2549_);
return v___x_2550_;
}
else
{
lean_object* v_head_2551_; lean_object* v_snd_2552_; lean_object* v_tail_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2565_; 
v_head_2551_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_head_2551_);
v_snd_2552_ = lean_ctor_get(v_head_2551_, 1);
v_tail_2553_ = lean_ctor_get(v_a_2548_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_a_2548_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v_a_2548_, 0);
lean_dec(v_unused_2566_);
v___x_2555_ = v_a_2548_;
v_isShared_2556_ = v_isSharedCheck_2565_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_tail_2553_);
lean_dec(v_a_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2565_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_snd_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v_snd_2557_ = lean_ctor_get(v_snd_2552_, 1);
v___x_2558_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2559_ = l_Lean_Expr_isAppOf(v_snd_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_del_object(v___x_2555_);
lean_dec(v_head_2551_);
v_a_2548_ = v_tail_2553_;
goto _start;
}
else
{
lean_object* v___x_2562_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v_a_2549_);
v___x_2562_ = v___x_2555_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_head_2551_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_a_2549_);
v___x_2562_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
v_a_2548_ = v_tail_2553_;
v_a_2549_ = v___x_2562_;
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
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0));
v___x_2569_ = l_Lean_stringToMessageData(v___x_2568_);
return v___x_2569_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(lean_object* v_as_x27_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
if (lean_obj_tag(v_as_x27_2570_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2571_);
return v___x_2575_;
}
else
{
lean_object* v_head_2576_; lean_object* v_snd_2577_; lean_object* v_tail_2578_; lean_object* v_fst_2579_; lean_object* v_fst_2580_; lean_object* v_snd_2581_; lean_object* v___x_2582_; 
v_head_2576_ = lean_ctor_get(v_as_x27_2570_, 0);
v_snd_2577_ = lean_ctor_get(v_head_2576_, 1);
v_tail_2578_ = lean_ctor_get(v_as_x27_2570_, 1);
v_fst_2579_ = lean_ctor_get(v_head_2576_, 0);
v_fst_2580_ = lean_ctor_get(v_snd_2577_, 0);
v_snd_2581_ = lean_ctor_get(v_snd_2577_, 1);
v___x_2582_ = lean_box(0);
if (lean_obj_tag(v_fst_2580_) == 1)
{
lean_object* v_str_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_str_2583_ = lean_ctor_get(v_fst_2580_, 1);
lean_inc_ref(v_str_2583_);
v___x_2584_ = l_Lean_Linter_List_stripBinderName(v_str_2583_);
v___x_2585_ = ((lean_object*)(l_Lean_Linter_List_allowedVectorNames));
v___x_2586_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2587_ = l_Lean_Linter_List_linter_listVariables;
v___x_2594_ = l_Lean_Expr_getAppNumArgs(v_snd_2581_);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_nat_sub(v___x_2594_, v___x_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = l_Lean_Expr_getRevArg_x21(v_snd_2581_, v___x_2596_);
v___x_2598_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2599_ = l_Lean_Expr_isAppOf(v___x_2597_, v___x_2598_);
lean_dec_ref(v___x_2597_);
if (v___x_2599_ == 0)
{
goto v___jp_2588_;
}
else
{
lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2601_ = lean_string_dec_eq(v___x_2584_, v___x_2600_);
if (v___x_2601_ == 0)
{
goto v___jp_2588_;
}
else
{
lean_dec_ref(v___x_2584_);
v_as_x27_2570_ = v_tail_2578_;
v_b_2571_ = v___x_2582_;
goto _start;
}
}
v___jp_2588_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2589_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
v___x_2590_ = l_Lean_stringToMessageData(v___x_2584_);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_inc(v_fst_2579_);
v___x_2592_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2587_, v_fst_2579_, v___x_2591_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref_known(v___x_2592_, 1);
v_as_x27_2570_ = v_tail_2578_;
v_b_2571_ = v___x_2582_;
goto _start;
}
else
{
return v___x_2592_;
}
}
}
else
{
lean_dec_ref(v___x_2584_);
v_as_x27_2570_ = v_tail_2578_;
v_b_2571_ = v___x_2582_;
goto _start;
}
}
else
{
v_as_x27_2570_ = v_tail_2578_;
v_b_2571_ = v___x_2582_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2570_ = stack[0].m_obj;
lean_object* v_b_2571_ = stack[1].m_obj;
lean_object* v___y_2572_ = stack[2].m_obj;
lean_object* v___y_2573_ = stack[3].m_obj;
lean_object* v_res_2605_;
v_res_2605_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_2570_, v_b_2571_, v___y_2572_, v___y_2573_);
stack->m_obj
 = v_res_2605_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(lean_object* v_as_x27_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_2606_, v_b_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v_as_x27_2606_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
if (lean_obj_tag(v_a_2612_) == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = l_List_reverse___redArg(v_a_2613_);
return v___x_2614_;
}
else
{
lean_object* v_head_2615_; lean_object* v_snd_2616_; lean_object* v_tail_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2629_; 
v_head_2615_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_head_2615_);
v_snd_2616_ = lean_ctor_get(v_head_2615_, 1);
v_tail_2617_ = lean_ctor_get(v_a_2612_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v_a_2612_, 0);
lean_dec(v_unused_2630_);
v___x_2619_ = v_a_2612_;
v_isShared_2620_ = v_isSharedCheck_2629_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_tail_2617_);
lean_dec(v_a_2612_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2629_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_snd_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_snd_2621_ = lean_ctor_get(v_snd_2616_, 1);
v___x_2622_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2623_ = l_Lean_Expr_isAppOf(v_snd_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_del_object(v___x_2619_);
lean_dec(v_head_2615_);
v_a_2612_ = v_tail_2617_;
goto _start;
}
else
{
lean_object* v___x_2626_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v_a_2613_);
v___x_2626_ = v___x_2619_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_head_2615_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_a_2613_);
v___x_2626_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
v_a_2612_ = v_tail_2617_;
v_a_2613_ = v___x_2626_;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(uint8_t v_v_2631_, lean_object* v_as_2632_, size_t v_sz_2633_, size_t v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_lt(v_i_2634_, v_sz_2633_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_b_2635_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v_a_2644_; lean_object* v___x_2645_; 
lean_dec_ref(v_b_2635_);
v___x_2641_ = lean_box(v_v_2631_);
v___f_2642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2642_, 0, v___x_2641_);
v___x_2643_ = lean_box(0);
v_a_2644_ = lean_array_uget_borrowed(v_as_2632_, v_i_2634_);
lean_inc(v_a_2644_);
v___x_2645_ = l_Lean_Linter_List_binders(v_a_2644_, v___f_2642_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_n(v_a_2646_, 2);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = lean_box(0);
v___x_2648_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2646_, v___x_2647_);
v___x_2649_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2648_, v___x_2643_, v___y_2636_, v___y_2637_);
lean_dec(v___x_2648_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref_known(v___x_2649_, 1);
lean_inc(v_a_2646_);
v___x_2650_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2646_, v___x_2647_);
v___x_2651_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2650_, v___x_2643_, v___y_2636_, v___y_2637_);
lean_dec(v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec_ref_known(v___x_2651_, 1);
v___x_2652_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2646_, v___x_2647_);
v___x_2653_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2652_, v___x_2643_, v___y_2636_, v___y_2637_);
lean_dec(v___x_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2654_; size_t v___x_2655_; size_t v___x_2656_; 
lean_dec_ref_known(v___x_2653_, 1);
v___x_2654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2655_ = ((size_t)1ULL);
v___x_2656_ = lean_usize_add(v_i_2634_, v___x_2655_);
v_i_2634_ = v___x_2656_;
v_b_2635_ = v___x_2654_;
goto _start;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_a_2658_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2653_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2653_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_a_2646_);
v_a_2666_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2651_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2651_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_a_2646_);
v_a_2674_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2649_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2649_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2694_; 
v_a_2682_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2684_ = v___x_2645_;
v_isShared_2685_ = v_isSharedCheck_2694_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2645_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2694_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v_ref_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v_ref_2686_ = lean_ctor_get(v___y_2636_, 7);
v___x_2687_ = lean_io_error_to_string(v_a_2682_);
v___x_2688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
v___x_2689_ = l_Lean_MessageData_ofFormat(v___x_2688_);
lean_inc(v_ref_2686_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_ref_2686_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2690_);
v___x_2692_ = v___x_2684_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_2631_ = stack[0].m_num;
lean_object* v_as_2632_ = stack[1].m_obj;
size_t v_sz_2633_ = stack[2].m_num;
size_t v_i_2634_ = stack[3].m_num;
lean_object* v_b_2635_ = stack[4].m_obj;
lean_object* v___y_2636_ = stack[5].m_obj;
lean_object* v___y_2637_ = stack[6].m_obj;
lean_object* v_res_2695_;
v_res_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v_v_2631_, v_as_2632_, v_sz_2633_, v_i_2634_, v_b_2635_, v___y_2636_, v___y_2637_);
stack->m_obj
 = v_res_2695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(lean_object* v_v_2696_, lean_object* v_as_2697_, lean_object* v_sz_2698_, lean_object* v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v_v_13315__boxed_2704_; size_t v_sz_boxed_2705_; size_t v_i_boxed_2706_; lean_object* v_res_2707_; 
v_v_13315__boxed_2704_ = lean_unbox(v_v_2696_);
v_sz_boxed_2705_ = lean_unbox_usize(v_sz_2698_);
lean_dec(v_sz_2698_);
v_i_boxed_2706_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v_v_13315__boxed_2704_, v_as_2697_, v_sz_boxed_2705_, v_i_boxed_2706_, v_b_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_as_2697_);
return v_res_2707_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(uint8_t v_v_2708_, lean_object* v_as_2709_, size_t v_sz_2710_, size_t v_i_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = lean_usize_dec_lt(v_i_2711_, v_sz_2710_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v_b_2712_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v_b_2712_);
v___x_2718_ = lean_box(v_v_2708_);
v___f_2719_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2719_, 0, v___x_2718_);
v___x_2720_ = lean_box(0);
v_a_2721_ = lean_array_uget_borrowed(v_as_2709_, v_i_2711_);
lean_inc(v_a_2721_);
v___x_2722_ = l_Lean_Linter_List_binders(v_a_2721_, v___f_2719_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc_n(v_a_2723_, 2);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2723_, v___x_2724_);
v___x_2726_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2725_, v___x_2720_, v___y_2713_, v___y_2714_);
lean_dec(v___x_2725_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref_known(v___x_2726_, 1);
lean_inc(v_a_2723_);
v___x_2727_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2723_, v___x_2724_);
v___x_2728_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2727_, v___x_2720_, v___y_2713_, v___y_2714_);
lean_dec(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref_known(v___x_2728_, 1);
v___x_2729_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2723_, v___x_2724_);
v___x_2730_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2729_, v___x_2720_, v___y_2713_, v___y_2714_);
lean_dec(v___x_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2730_, 1);
v___x_2731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2711_, v___x_2732_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v_v_2708_, v_as_2709_, v_sz_2710_, v___x_2733_, v___x_2731_, v___y_2713_, v___y_2714_);
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_a_2735_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2730_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2730_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2723_);
v_a_2743_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2728_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2728_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2723_);
v_a_2751_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2726_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2726_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2771_; 
v_a_2759_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2761_ = v___x_2722_;
v_isShared_2762_ = v_isSharedCheck_2771_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2722_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2771_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_ref_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v_ref_2763_ = lean_ctor_get(v___y_2713_, 7);
v___x_2764_ = lean_io_error_to_string(v_a_2759_);
v___x_2765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v___x_2766_ = l_Lean_MessageData_ofFormat(v___x_2765_);
lean_inc(v_ref_2763_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_ref_2763_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2767_);
v___x_2769_ = v___x_2761_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_2708_ = stack[0].m_num;
lean_object* v_as_2709_ = stack[1].m_obj;
size_t v_sz_2710_ = stack[2].m_num;
size_t v_i_2711_ = stack[3].m_num;
lean_object* v_b_2712_ = stack[4].m_obj;
lean_object* v___y_2713_ = stack[5].m_obj;
lean_object* v___y_2714_ = stack[6].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v_v_2708_, v_as_2709_, v_sz_2710_, v_i_2711_, v_b_2712_, v___y_2713_, v___y_2714_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(lean_object* v_v_2773_, lean_object* v_as_2774_, lean_object* v_sz_2775_, lean_object* v_i_2776_, lean_object* v_b_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v_v_13504__boxed_2781_; size_t v_sz_boxed_2782_; size_t v_i_boxed_2783_; lean_object* v_res_2784_; 
v_v_13504__boxed_2781_ = lean_unbox(v_v_2773_);
v_sz_boxed_2782_ = lean_unbox_usize(v_sz_2775_);
lean_dec(v_sz_2775_);
v_i_boxed_2783_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v_v_13504__boxed_2781_, v_as_2774_, v_sz_boxed_2782_, v_i_boxed_2783_, v_b_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v_as_2774_);
return v_res_2784_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(lean_object* v_init_2785_, uint8_t v_v_2786_, lean_object* v_n_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
if (lean_obj_tag(v_n_2787_) == 0)
{
lean_object* v_cs_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; size_t v_sz_2795_; size_t v___x_2796_; lean_object* v___x_2797_; 
v_cs_2792_ = lean_ctor_get(v_n_2787_, 0);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_b_2788_);
v_sz_2795_ = lean_array_size(v_cs_2792_);
v___x_2796_ = ((size_t)0ULL);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2785_, v_v_2786_, v_cs_2792_, v_sz_2795_, v___x_2796_, v___x_2794_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2812_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2812_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2812_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v_fst_2802_; 
v_fst_2802_ = lean_ctor_get(v_a_2798_, 0);
if (lean_obj_tag(v_fst_2802_) == 0)
{
lean_object* v_snd_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v_snd_2803_ = lean_ctor_get(v_a_2798_, 1);
lean_inc(v_snd_2803_);
lean_dec(v_a_2798_);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_snd_2803_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2804_);
v___x_2806_ = v___x_2800_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
lean_object* v_val_2808_; lean_object* v___x_2810_; 
lean_inc_ref(v_fst_2802_);
lean_dec(v_a_2798_);
v_val_2808_ = lean_ctor_get(v_fst_2802_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_fst_2802_, 1);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v_val_2808_);
v___x_2810_ = v___x_2800_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_val_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2797_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2797_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_vs_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; size_t v_sz_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v_vs_2821_ = lean_ctor_get(v_n_2787_, 0);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v_b_2788_);
v_sz_2824_ = lean_array_size(v_vs_2821_);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v_v_2786_, v_vs_2821_, v_sz_2824_, v___x_2825_, v___x_2823_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2841_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2841_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2841_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_fst_2831_; 
v_fst_2831_ = lean_ctor_get(v_a_2827_, 0);
if (lean_obj_tag(v_fst_2831_) == 0)
{
lean_object* v_snd_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v_snd_2832_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_snd_2832_);
lean_dec(v_a_2827_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_snd_2832_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2833_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
else
{
lean_object* v_val_2837_; lean_object* v___x_2839_; 
lean_inc_ref(v_fst_2831_);
lean_dec(v_a_2827_);
v_val_2837_ = lean_ctor_get(v_fst_2831_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v_fst_2831_, 1);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v_val_2837_);
v___x_2839_ = v___x_2829_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_val_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2842_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2826_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2826_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2785_ = stack[0].m_obj;
uint8_t v_v_2786_ = stack[1].m_num;
lean_object* v_n_2787_ = stack[2].m_obj;
lean_object* v_b_2788_ = stack[3].m_obj;
lean_object* v___y_2789_ = stack[4].m_obj;
lean_object* v___y_2790_ = stack[5].m_obj;
lean_object* v_res_2850_;
v_res_2850_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2785_, v_v_2786_, v_n_2787_, v_b_2788_, v___y_2789_, v___y_2790_);
stack->m_obj
 = v_res_2850_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(lean_object* v_init_2851_, uint8_t v_v_2852_, lean_object* v_as_2853_, size_t v_sz_2854_, size_t v_i_2855_, lean_object* v_b_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_usize_dec_lt(v_i_2855_, v_sz_2854_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_b_2856_);
return v___x_2861_;
}
else
{
lean_object* v_snd_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2896_; 
v_snd_2862_ = lean_ctor_get(v_b_2856_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_b_2856_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v_b_2856_, 0);
lean_dec(v_unused_2897_);
v___x_2864_ = v_b_2856_;
v_isShared_2865_ = v_isSharedCheck_2896_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_snd_2862_);
lean_dec(v_b_2856_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2896_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_box(0);
v_a_2867_ = lean_array_uget_borrowed(v_as_2853_, v_i_2855_);
lean_inc(v_snd_2862_);
v___x_2868_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2851_, v_v_2852_, v_a_2867_, v_snd_2862_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2887_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_a_2869_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2873_);
v___x_2875_ = v___x_2864_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_snd_2862_);
v___x_2875_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2875_);
v___x_2877_ = v___x_2871_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; 
lean_del_object(v___x_2871_);
lean_dec(v_snd_2862_);
v_a_2880_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v_a_2869_, 1);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v_a_2880_);
lean_ctor_set(v___x_2864_, 0, v___x_2866_);
v___x_2882_ = v___x_2864_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_a_2880_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
size_t v___x_2883_; size_t v___x_2884_; 
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_i_2855_, v___x_2883_);
v_i_2855_ = v___x_2884_;
v_b_2856_ = v___x_2882_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_del_object(v___x_2864_);
lean_dec(v_snd_2862_);
v_a_2888_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2868_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2868_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2851_ = stack[0].m_obj;
uint8_t v_v_2852_ = stack[1].m_num;
lean_object* v_as_2853_ = stack[2].m_obj;
size_t v_sz_2854_ = stack[3].m_num;
size_t v_i_2855_ = stack[4].m_num;
lean_object* v_b_2856_ = stack[5].m_obj;
lean_object* v___y_2857_ = stack[6].m_obj;
lean_object* v___y_2858_ = stack[7].m_obj;
lean_object* v_res_2898_;
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2851_, v_v_2852_, v_as_2853_, v_sz_2854_, v_i_2855_, v_b_2856_, v___y_2857_, v___y_2858_);
stack->m_obj
 = v_res_2898_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(lean_object* v_init_2899_, lean_object* v_v_2900_, lean_object* v_as_2901_, lean_object* v_sz_2902_, lean_object* v_i_2903_, lean_object* v_b_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
uint8_t v_v_13690__boxed_2908_; size_t v_sz_boxed_2909_; size_t v_i_boxed_2910_; lean_object* v_res_2911_; 
v_v_13690__boxed_2908_ = lean_unbox(v_v_2900_);
v_sz_boxed_2909_ = lean_unbox_usize(v_sz_2902_);
lean_dec(v_sz_2902_);
v_i_boxed_2910_ = lean_unbox_usize(v_i_2903_);
lean_dec(v_i_2903_);
v_res_2911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2899_, v_v_13690__boxed_2908_, v_as_2901_, v_sz_boxed_2909_, v_i_boxed_2910_, v_b_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec_ref(v_as_2901_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(lean_object* v_init_2912_, lean_object* v_v_2913_, lean_object* v_n_2914_, lean_object* v_b_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v_v_13710__boxed_2919_; lean_object* v_res_2920_; 
v_v_13710__boxed_2919_ = lean_unbox(v_v_2913_);
v_res_2920_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2912_, v_v_13710__boxed_2919_, v_n_2914_, v_b_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v_n_2914_);
return v_res_2920_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(uint8_t v_v_2921_, lean_object* v_as_2922_, size_t v_sz_2923_, size_t v_i_2924_, lean_object* v_b_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_usize_dec_lt(v_i_2924_, v_sz_2923_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_b_2925_);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; lean_object* v_a_2934_; lean_object* v___x_2935_; 
lean_dec_ref(v_b_2925_);
v___x_2931_ = lean_box(v_v_2921_);
v___f_2932_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2932_, 0, v___x_2931_);
v___x_2933_ = lean_box(0);
v_a_2934_ = lean_array_uget_borrowed(v_as_2922_, v_i_2924_);
lean_inc(v_a_2934_);
v___x_2935_ = l_Lean_Linter_List_binders(v_a_2934_, v___f_2932_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_n(v_a_2936_, 2);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = lean_box(0);
v___x_2938_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2936_, v___x_2937_);
v___x_2939_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2938_, v___x_2933_, v___y_2926_, v___y_2927_);
lean_dec(v___x_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref_known(v___x_2939_, 1);
lean_inc(v_a_2936_);
v___x_2940_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2936_, v___x_2937_);
v___x_2941_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2940_, v___x_2933_, v___y_2926_, v___y_2927_);
lean_dec(v___x_2940_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec_ref_known(v___x_2941_, 1);
v___x_2942_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2936_, v___x_2937_);
v___x_2943_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2942_, v___x_2933_, v___y_2926_, v___y_2927_);
lean_dec(v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; 
lean_dec_ref_known(v___x_2943_, 1);
v___x_2944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2924_, v___x_2945_);
v_i_2924_ = v___x_2946_;
v_b_2925_ = v___x_2944_;
goto _start;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2943_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2943_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2936_);
v_a_2956_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2941_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2941_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_a_2936_);
v_a_2964_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2939_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2939_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2984_; 
v_a_2972_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2974_ = v___x_2935_;
v_isShared_2975_ = v_isSharedCheck_2984_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2935_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2984_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v_ref_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v_ref_2976_ = lean_ctor_get(v___y_2926_, 7);
v___x_2977_ = lean_io_error_to_string(v_a_2972_);
v___x_2978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
v___x_2979_ = l_Lean_MessageData_ofFormat(v___x_2978_);
lean_inc(v_ref_2976_);
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_ref_2976_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2980_);
v___x_2982_ = v___x_2974_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_2921_ = stack[0].m_num;
lean_object* v_as_2922_ = stack[1].m_obj;
size_t v_sz_2923_ = stack[2].m_num;
size_t v_i_2924_ = stack[3].m_num;
lean_object* v_b_2925_ = stack[4].m_obj;
lean_object* v___y_2926_ = stack[5].m_obj;
lean_object* v___y_2927_ = stack[6].m_obj;
lean_object* v_res_2985_;
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v_v_2921_, v_as_2922_, v_sz_2923_, v_i_2924_, v_b_2925_, v___y_2926_, v___y_2927_);
stack->m_obj
 = v_res_2985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_v_2986_, lean_object* v_as_2987_, lean_object* v_sz_2988_, lean_object* v_i_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v_v_13998__boxed_2994_; size_t v_sz_boxed_2995_; size_t v_i_boxed_2996_; lean_object* v_res_2997_; 
v_v_13998__boxed_2994_ = lean_unbox(v_v_2986_);
v_sz_boxed_2995_ = lean_unbox_usize(v_sz_2988_);
lean_dec(v_sz_2988_);
v_i_boxed_2996_ = lean_unbox_usize(v_i_2989_);
lean_dec(v_i_2989_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v_v_13998__boxed_2994_, v_as_2987_, v_sz_boxed_2995_, v_i_boxed_2996_, v_b_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v_as_2987_);
return v_res_2997_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(uint8_t v_v_2998_, lean_object* v_as_2999_, size_t v_sz_3000_, size_t v_i_3001_, lean_object* v_b_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_lt(v_i_3001_, v_sz_3000_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_b_3002_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v_b_3002_);
v___x_3008_ = lean_box(v_v_2998_);
v___f_3009_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3009_, 0, v___x_3008_);
v___x_3010_ = lean_box(0);
v_a_3011_ = lean_array_uget_borrowed(v_as_2999_, v_i_3001_);
lean_inc(v_a_3011_);
v___x_3012_ = l_Lean_Linter_List_binders(v_a_3011_, v___f_3009_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_n(v_a_3013_, 2);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_box(0);
v___x_3015_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_3013_, v___x_3014_);
v___x_3016_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_3015_, v___x_3010_, v___y_3003_, v___y_3004_);
lean_dec(v___x_3015_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3016_, 1);
lean_inc(v_a_3013_);
v___x_3017_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_3013_, v___x_3014_);
v___x_3018_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_3017_, v___x_3010_, v___y_3003_, v___y_3004_);
lean_dec(v___x_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_3013_, v___x_3014_);
v___x_3020_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_3019_, v___x_3010_, v___y_3003_, v___y_3004_);
lean_dec(v___x_3019_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_add(v_i_3001_, v___x_3022_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v_v_2998_, v_as_2999_, v_sz_3000_, v___x_3023_, v___x_3021_, v___y_3003_, v___y_3004_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
v_a_3025_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3020_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3020_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_a_3013_);
v_a_3033_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3018_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3018_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_a_3013_);
v_a_3041_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3016_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3016_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3061_; 
v_a_3049_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3051_ = v___x_3012_;
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3012_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_ref_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v_ref_3053_ = lean_ctor_get(v___y_3003_, 7);
v___x_3054_ = lean_io_error_to_string(v_a_3049_);
v___x_3055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = l_Lean_MessageData_ofFormat(v___x_3055_);
lean_inc(v_ref_3053_);
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v_ref_3053_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3057_);
v___x_3059_ = v___x_3051_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_2998_ = stack[0].m_num;
lean_object* v_as_2999_ = stack[1].m_obj;
size_t v_sz_3000_ = stack[2].m_num;
size_t v_i_3001_ = stack[3].m_num;
lean_object* v_b_3002_ = stack[4].m_obj;
lean_object* v___y_3003_ = stack[5].m_obj;
lean_object* v___y_3004_ = stack[6].m_obj;
lean_object* v_res_3062_;
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v_v_2998_, v_as_2999_, v_sz_3000_, v_i_3001_, v_b_3002_, v___y_3003_, v___y_3004_);
stack->m_obj
 = v_res_3062_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(lean_object* v_v_3063_, lean_object* v_as_3064_, lean_object* v_sz_3065_, lean_object* v_i_3066_, lean_object* v_b_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
uint8_t v_v_14187__boxed_3071_; size_t v_sz_boxed_3072_; size_t v_i_boxed_3073_; lean_object* v_res_3074_; 
v_v_14187__boxed_3071_ = lean_unbox(v_v_3063_);
v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3065_);
lean_dec(v_sz_3065_);
v_i_boxed_3073_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v_v_14187__boxed_3071_, v_as_3064_, v_sz_boxed_3072_, v_i_boxed_3073_, v_b_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v_as_3064_);
return v_res_3074_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(uint8_t v_v_3075_, lean_object* v_t_3076_, lean_object* v_init_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_root_3081_; lean_object* v_tail_3082_; lean_object* v___x_3083_; 
v_root_3081_ = lean_ctor_get(v_t_3076_, 0);
v_tail_3082_ = lean_ctor_get(v_t_3076_, 1);
v___x_3083_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_3077_, v_v_3075_, v_root_3081_, v_init_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3120_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3120_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3120_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
if (lean_obj_tag(v_a_3084_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3090_; 
v_a_3088_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v_a_3084_, 1);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v_a_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; size_t v_sz_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
lean_del_object(v___x_3086_);
v_a_3092_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v_a_3084_, 1);
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_a_3092_);
v_sz_3095_ = lean_array_size(v_tail_3082_);
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v_v_3075_, v_tail_3082_, v_sz_3095_, v___x_3096_, v___x_3094_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3111_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3111_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3111_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_fst_3102_; 
v_fst_3102_ = lean_ctor_get(v_a_3098_, 0);
if (lean_obj_tag(v_fst_3102_) == 0)
{
lean_object* v_snd_3103_; lean_object* v___x_3105_; 
v_snd_3103_ = lean_ctor_get(v_a_3098_, 1);
lean_inc(v_snd_3103_);
lean_dec(v_a_3098_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v_snd_3103_);
v___x_3105_ = v___x_3100_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_snd_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3109_; 
lean_inc_ref(v_fst_3102_);
lean_dec(v_a_3098_);
v_val_3107_ = lean_ctor_get(v_fst_3102_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v_fst_3102_, 1);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v_val_3107_);
v___x_3109_ = v___x_3100_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_val_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_a_3112_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3097_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3097_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3083_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3083_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_3075_ = stack[0].m_num;
lean_object* v_t_3076_ = stack[1].m_obj;
lean_object* v_init_3077_ = stack[2].m_obj;
lean_object* v___y_3078_ = stack[3].m_obj;
lean_object* v___y_3079_ = stack[4].m_obj;
lean_object* v_res_3129_;
v_res_3129_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_v_3075_, v_t_3076_, v_init_3077_, v___y_3078_, v___y_3079_);
stack->m_obj
 = v_res_3129_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(lean_object* v_v_3130_, lean_object* v_t_3131_, lean_object* v_init_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
uint8_t v_v_14373__boxed_3136_; lean_object* v_res_3137_; 
v_v_14373__boxed_3136_ = lean_unbox(v_v_3130_);
v_res_3137_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_v_14373__boxed_3136_, v_t_3131_, v_init_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v_t_3131_);
return v_res_3137_;
}
}
lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0(lean_object* v_stx_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v_scopes_3147_; lean_object* v___x_3148_; lean_object* v_opts_3149_; lean_object* v___x_3150_; lean_object* v_name_3151_; lean_object* v_map_3152_; lean_object* v___x_3153_; 
v___x_3142_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3143_ = lean_st_ref_get(v___y_3140_);
v_scopes_3147_ = lean_ctor_get(v___x_3143_, 2);
lean_inc(v_scopes_3147_);
lean_dec(v___x_3143_);
v___x_3148_ = l_List_head_x21___redArg(v___x_3142_, v_scopes_3147_);
lean_dec(v_scopes_3147_);
v_opts_3149_ = lean_ctor_get(v___x_3148_, 1);
lean_inc_ref(v_opts_3149_);
lean_dec(v___x_3148_);
v___x_3150_ = l_Lean_Linter_List_linter_listVariables;
v_name_3151_ = lean_ctor_get(v___x_3150_, 0);
v_map_3152_ = lean_ctor_get(v_opts_3149_, 0);
lean_inc(v_map_3152_);
lean_dec_ref(v_opts_3149_);
v___x_3153_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3152_, v_name_3151_);
lean_dec(v_map_3152_);
if (lean_obj_tag(v___x_3153_) == 0)
{
goto v___jp_3144_;
}
else
{
lean_object* v_val_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3186_; 
v_val_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3186_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_val_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3186_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
if (lean_obj_tag(v_val_3154_) == 1)
{
uint8_t v_v_3158_; 
v_v_3158_ = lean_ctor_get_uint8(v_val_3154_, 0);
lean_dec_ref_known(v_val_3154_, 0);
if (v_v_3158_ == 0)
{
lean_del_object(v___x_3156_);
goto v___jp_3144_;
}
else
{
lean_object* v___x_3159_; lean_object* v_messages_3160_; uint8_t v___x_3161_; 
v___x_3159_ = lean_st_ref_get(v___y_3140_);
v_messages_3160_ = lean_ctor_get(v___x_3159_, 1);
lean_inc_ref(v_messages_3160_);
lean_dec(v___x_3159_);
v___x_3161_ = l_Lean_MessageLog_hasErrors(v_messages_3160_);
lean_dec_ref(v_messages_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v_infoState_3168_; uint8_t v_enabled_3169_; 
v___x_3162_ = lean_st_ref_get(v___y_3140_);
v_infoState_3168_ = lean_ctor_get(v___x_3162_, 8);
lean_inc_ref(v_infoState_3168_);
lean_dec(v___x_3162_);
v_enabled_3169_ = lean_ctor_get_uint8(v_infoState_3168_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3168_);
if (v_enabled_3169_ == 0)
{
goto v___jp_3163_;
}
else
{
if (v___x_3161_ == 0)
{
lean_object* v___x_3170_; lean_object* v_a_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_del_object(v___x_3156_);
v___x_3170_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_3140_);
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
v___x_3172_ = lean_box(0);
v___x_3173_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_v_3158_, v_a_3171_, v___x_3172_, v___y_3139_, v___y_3140_);
lean_dec(v_a_3171_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3173_, 0);
lean_dec(v_unused_3181_);
v___x_3175_ = v___x_3173_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3173_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3172_);
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3172_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
else
{
return v___x_3173_;
}
}
else
{
goto v___jp_3163_;
}
}
v___jp_3163_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_box(0);
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3164_);
v___x_3166_ = v___x_3156_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_box(0);
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3182_);
v___x_3184_ = v___x_3156_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_del_object(v___x_3156_);
lean_dec(v_val_3154_);
goto v___jp_3144_;
}
}
}
v___jp_3144_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_List_listVariablesLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3138_ = stack[0].m_obj;
lean_object* v___y_3139_ = stack[1].m_obj;
lean_object* v___y_3140_ = stack[2].m_obj;
lean_object* v_res_3187_;
v_res_3187_ = l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_3138_, v___y_3139_, v___y_3140_);
stack->m_obj
 = v_res_3187_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(lean_object* v_stx_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v_stx_3188_);
return v_res_3192_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(lean_object* v_as_3206_, lean_object* v_as_x27_3207_, lean_object* v_b_3208_, lean_object* v_a_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_3207_, v_b_3208_, v___y_3210_, v___y_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3206_ = stack[0].m_obj;
lean_object* v_as_x27_3207_ = stack[1].m_obj;
lean_object* v_b_3208_ = stack[2].m_obj;
lean_object* v___y_3210_ = stack[4].m_obj;
lean_object* v___y_3211_ = stack[5].m_obj;
lean_object* v_res_3214_;
v_res_3214_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(v_as_3206_, v_as_x27_3207_, v_b_3208_, lean_box(0), v___y_3210_, v___y_3211_);
stack->m_obj
 = v_res_3214_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(lean_object* v_as_3215_, lean_object* v_as_x27_3216_, lean_object* v_b_3217_, lean_object* v_a_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(v_as_3215_, v_as_x27_3216_, v_b_3217_, v_a_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v_as_x27_3216_);
lean_dec(v_as_3215_);
return v_res_3222_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(lean_object* v_as_3223_, lean_object* v_as_x27_3224_, lean_object* v_b_3225_, lean_object* v_a_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_3224_, v_b_3225_, v___y_3227_, v___y_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3223_ = stack[0].m_obj;
lean_object* v_as_x27_3224_ = stack[1].m_obj;
lean_object* v_b_3225_ = stack[2].m_obj;
lean_object* v___y_3227_ = stack[4].m_obj;
lean_object* v___y_3228_ = stack[5].m_obj;
lean_object* v_res_3231_;
v_res_3231_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(v_as_3223_, v_as_x27_3224_, v_b_3225_, lean_box(0), v___y_3227_, v___y_3228_);
stack->m_obj
 = v_res_3231_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(lean_object* v_as_3232_, lean_object* v_as_x27_3233_, lean_object* v_b_3234_, lean_object* v_a_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(v_as_3232_, v_as_x27_3233_, v_b_3234_, v_a_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v_as_x27_3233_);
lean_dec(v_as_3232_);
return v_res_3239_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(lean_object* v_as_3240_, lean_object* v_as_x27_3241_, lean_object* v_b_3242_, lean_object* v_a_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_3241_, v_b_3242_, v___y_3244_, v___y_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3240_ = stack[0].m_obj;
lean_object* v_as_x27_3241_ = stack[1].m_obj;
lean_object* v_b_3242_ = stack[2].m_obj;
lean_object* v___y_3244_ = stack[4].m_obj;
lean_object* v___y_3245_ = stack[5].m_obj;
lean_object* v_res_3248_;
v_res_3248_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(v_as_3240_, v_as_x27_3241_, v_b_3242_, lean_box(0), v___y_3244_, v___y_3245_);
stack->m_obj
 = v_res_3248_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(lean_object* v_as_3249_, lean_object* v_as_x27_3250_, lean_object* v_b_3251_, lean_object* v_a_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(v_as_3249_, v_as_x27_3250_, v_b_3251_, v_a_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v_as_x27_3250_);
lean_dec(v_as_3249_);
return v_res_3256_;
}
}
lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l_Lean_Linter_List_listVariablesLinter));
v___x_3259_ = l_Lean_Elab_Command_addLinter(v___x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3260_;
v_res_3260_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
return v_res_3262_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
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
