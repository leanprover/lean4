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
lean_dec_ref(v_i_257_);
lean_dec_ref_known(v_info_255_, 1);
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
lean_dec_ref(v_i_257_);
lean_dec_ref_known(v_info_255_, 1);
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
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(lean_object* v_s_590_){
_start:
{
lean_object* v_str_591_; lean_object* v_startInclusive_592_; lean_object* v_endExclusive_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_str_591_ = lean_ctor_get(v_s_590_, 0);
v_startInclusive_592_ = lean_ctor_get(v_s_590_, 1);
v_endExclusive_593_ = lean_ctor_get(v_s_590_, 2);
v___x_594_ = lean_unsigned_to_nat(3u);
v___x_595_ = lean_nat_sub(v_endExclusive_593_, v_startInclusive_592_);
v___x_596_ = lean_nat_dec_le(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v___x_595_);
return v_s_590_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_597_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0));
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_sub(v___x_595_, v___x_594_);
lean_dec(v___x_595_);
v___x_600_ = lean_nat_add(v_startInclusive_592_, v___x_599_);
v___x_601_ = lean_string_memcmp(v_str_591_, v___x_597_, v___x_600_, v___x_598_, v___x_594_);
lean_dec(v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v___x_599_);
return v_s_590_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
lean_inc(v_startInclusive_592_);
lean_inc_ref(v_str_591_);
v___x_602_ = l_String_Slice_pos_x21(v_s_590_, v___x_599_);
lean_dec(v___x_599_);
v_isSharedCheck_610_ = !lean_is_exclusive(v_s_590_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; lean_object* v_unused_613_; 
v_unused_611_ = lean_ctor_get(v_s_590_, 2);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_s_590_, 1);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_s_590_, 0);
lean_dec(v_unused_613_);
v___x_604_ = v_s_590_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_s_590_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_nat_add(v_startInclusive_592_, v___x_602_);
lean_dec(v___x_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_str_591_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_startInclusive_592_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(lean_object* v_s_615_){
_start:
{
lean_object* v_str_616_; lean_object* v_startInclusive_617_; lean_object* v_endExclusive_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_str_616_ = lean_ctor_get(v_s_615_, 0);
v_startInclusive_617_ = lean_ctor_get(v_s_615_, 1);
v_endExclusive_618_ = lean_ctor_get(v_s_615_, 2);
v___x_619_ = lean_unsigned_to_nat(3u);
v___x_620_ = lean_nat_sub(v_endExclusive_618_, v_startInclusive_617_);
v___x_621_ = lean_nat_dec_le(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v___x_620_);
return v_s_615_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_622_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0));
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_sub(v___x_620_, v___x_619_);
lean_dec(v___x_620_);
v___x_625_ = lean_nat_add(v_startInclusive_617_, v___x_624_);
v___x_626_ = lean_string_memcmp(v_str_616_, v___x_622_, v___x_625_, v___x_623_, v___x_619_);
lean_dec(v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v___x_624_);
return v_s_615_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
lean_inc(v_startInclusive_617_);
lean_inc_ref(v_str_616_);
v___x_627_ = l_String_Slice_pos_x21(v_s_615_, v___x_624_);
lean_dec(v___x_624_);
v_isSharedCheck_635_ = !lean_is_exclusive(v_s_615_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_636_ = lean_ctor_get(v_s_615_, 2);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_s_615_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_s_615_, 0);
lean_dec(v_unused_638_);
v___x_629_ = v_s_615_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_dec(v_s_615_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_nat_add(v_startInclusive_617_, v___x_627_);
lean_dec(v___x_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 2, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_str_616_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_startInclusive_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(lean_object* v_s_640_){
_start:
{
lean_object* v_str_641_; lean_object* v_startInclusive_642_; lean_object* v_endExclusive_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_str_641_ = lean_ctor_get(v_s_640_, 0);
v_startInclusive_642_ = lean_ctor_get(v_s_640_, 1);
v_endExclusive_643_ = lean_ctor_get(v_s_640_, 2);
v___x_644_ = lean_unsigned_to_nat(3u);
v___x_645_ = lean_nat_sub(v_endExclusive_643_, v_startInclusive_642_);
v___x_646_ = lean_nat_dec_le(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec(v___x_645_);
return v_s_640_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_647_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0));
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_sub(v___x_645_, v___x_644_);
lean_dec(v___x_645_);
v___x_650_ = lean_nat_add(v_startInclusive_642_, v___x_649_);
v___x_651_ = lean_string_memcmp(v_str_641_, v___x_647_, v___x_650_, v___x_648_, v___x_644_);
lean_dec(v___x_650_);
if (v___x_651_ == 0)
{
lean_dec(v___x_649_);
return v_s_640_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
lean_inc(v_startInclusive_642_);
lean_inc_ref(v_str_641_);
v___x_652_ = l_String_Slice_pos_x21(v_s_640_, v___x_649_);
lean_dec(v___x_649_);
v_isSharedCheck_660_ = !lean_is_exclusive(v_s_640_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; lean_object* v_unused_662_; lean_object* v_unused_663_; 
v_unused_661_ = lean_ctor_get(v_s_640_, 2);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v_s_640_, 1);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v_s_640_, 0);
lean_dec(v_unused_663_);
v___x_654_ = v_s_640_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_s_640_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_nat_add(v_startInclusive_642_, v___x_652_);
lean_dec(v___x_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 2, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_str_641_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_startInclusive_642_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(lean_object* v_s_665_){
_start:
{
lean_object* v_str_666_; lean_object* v_startInclusive_667_; lean_object* v_endExclusive_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_str_666_ = lean_ctor_get(v_s_665_, 0);
v_startInclusive_667_ = lean_ctor_get(v_s_665_, 1);
v_endExclusive_668_ = lean_ctor_get(v_s_665_, 2);
v___x_669_ = lean_unsigned_to_nat(3u);
v___x_670_ = lean_nat_sub(v_endExclusive_668_, v_startInclusive_667_);
v___x_671_ = lean_nat_dec_le(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v___x_670_);
return v_s_665_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_672_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0));
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_sub(v___x_670_, v___x_669_);
lean_dec(v___x_670_);
v___x_675_ = lean_nat_add(v_startInclusive_667_, v___x_674_);
v___x_676_ = lean_string_memcmp(v_str_666_, v___x_672_, v___x_675_, v___x_673_, v___x_669_);
lean_dec(v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v___x_674_);
return v_s_665_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
lean_inc(v_startInclusive_667_);
lean_inc_ref(v_str_666_);
v___x_677_ = l_String_Slice_pos_x21(v_s_665_, v___x_674_);
lean_dec(v___x_674_);
v_isSharedCheck_685_ = !lean_is_exclusive(v_s_665_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; 
v_unused_686_ = lean_ctor_get(v_s_665_, 2);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_s_665_, 1);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_s_665_, 0);
lean_dec(v_unused_688_);
v___x_679_ = v_s_665_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_s_665_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = lean_nat_add(v_startInclusive_667_, v___x_677_);
lean_dec(v___x_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 2, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_str_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_startInclusive_667_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(lean_object* v_s_690_){
_start:
{
lean_object* v_str_691_; lean_object* v_startInclusive_692_; lean_object* v_endExclusive_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_str_691_ = lean_ctor_get(v_s_690_, 0);
v_startInclusive_692_ = lean_ctor_get(v_s_690_, 1);
v_endExclusive_693_ = lean_ctor_get(v_s_690_, 2);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_sub(v_endExclusive_693_, v_startInclusive_692_);
v___x_696_ = lean_nat_dec_le(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec(v___x_695_);
return v_s_690_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_697_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_sub(v___x_695_, v___x_694_);
lean_dec(v___x_695_);
v___x_700_ = lean_nat_add(v_startInclusive_692_, v___x_699_);
v___x_701_ = lean_string_memcmp(v_str_691_, v___x_697_, v___x_700_, v___x_698_, v___x_694_);
lean_dec(v___x_700_);
if (v___x_701_ == 0)
{
lean_dec(v___x_699_);
return v_s_690_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
lean_inc(v_startInclusive_692_);
lean_inc_ref(v_str_691_);
v___x_702_ = l_String_Slice_pos_x21(v_s_690_, v___x_699_);
lean_dec(v___x_699_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_s_690_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_711_ = lean_ctor_get(v_s_690_, 2);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_s_690_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_s_690_, 0);
lean_dec(v_unused_713_);
v___x_704_ = v_s_690_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_s_690_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_nat_add(v_startInclusive_692_, v___x_702_);
lean_dec(v___x_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 2, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_str_691_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_startInclusive_692_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(lean_object* v_s_714_, lean_object* v_pat_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_string_utf8_byte_size(v_s_714_);
v___x_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_718_, 0, v_s_714_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(lean_object* v_s_720_, lean_object* v_pat_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_720_, v_pat_721_);
lean_dec_ref(v_pat_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_stripBinderName(lean_object* v_s_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_str_730_; lean_object* v_startInclusive_731_; lean_object* v_endExclusive_732_; lean_object* v___x_733_; 
v___x_724_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0));
v___x_725_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(v_s_723_, v___x_724_);
v___x_726_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(v___x_725_);
v___x_727_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(v___x_726_);
v___x_728_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(v___x_727_);
v___x_729_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(v___x_728_);
v_str_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_str_730_);
v_startInclusive_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_startInclusive_731_);
v_endExclusive_732_ = lean_ctor_get(v___x_729_, 2);
lean_inc(v_endExclusive_732_);
lean_dec_ref(v___x_729_);
v___x_733_ = lean_string_utf8_extract_fast(v_str_730_, v_startInclusive_731_, v_endExclusive_732_);
lean_dec(v_endExclusive_732_);
lean_dec(v_startInclusive_731_);
lean_dec_ref(v_str_730_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(lean_object* v_pat_734_, lean_object* v_s_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v_s_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(lean_object* v_pat_737_, lean_object* v_s_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(v_pat_737_, v_s_738_);
lean_dec_ref(v_pat_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; lean_object* v_infoState_793_; lean_object* v_trees_794_; lean_object* v___x_795_; 
v___x_792_ = lean_st_ref_get(v___y_790_);
v_infoState_793_ = lean_ctor_get(v___x_792_, 8);
lean_inc_ref(v_infoState_793_);
lean_dec(v___x_792_);
v_trees_794_ = lean_ctor_get(v_infoState_793_, 2);
lean_inc_ref(v_trees_794_);
lean_dec_ref(v_infoState_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_trees_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_796_);
lean_dec(v___y_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(lean_object* v_opts_807_, lean_object* v_opt_808_){
_start:
{
lean_object* v_name_809_; lean_object* v_defValue_810_; lean_object* v_map_811_; lean_object* v___x_812_; 
v_name_809_ = lean_ctor_get(v_opt_808_, 0);
v_defValue_810_ = lean_ctor_get(v_opt_808_, 1);
v_map_811_ = lean_ctor_get(v_opts_807_, 0);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_811_, v_name_809_);
if (lean_obj_tag(v___x_812_) == 0)
{
uint8_t v___x_813_; 
v___x_813_ = lean_unbox(v_defValue_810_);
return v___x_813_;
}
else
{
lean_object* v_val_814_; 
v_val_814_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v___x_812_, 1);
if (lean_obj_tag(v_val_814_) == 1)
{
uint8_t v_v_815_; 
v_v_815_ = lean_ctor_get_uint8(v_val_814_, 0);
lean_dec_ref_known(v_val_814_, 0);
return v_v_815_;
}
else
{
uint8_t v___x_816_; 
lean_dec(v_val_814_);
v___x_816_ = lean_unbox(v_defValue_810_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_opts_817_, lean_object* v_opt_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_817_, v_opt_818_);
lean_dec_ref(v_opt_818_);
lean_dec_ref(v_opts_817_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_822_, uint8_t v___y_823_, lean_object* v_x_824_){
_start:
{
if (lean_obj_tag(v_x_824_) == 1)
{
lean_object* v_pre_825_; 
v_pre_825_ = lean_ctor_get(v_x_824_, 0);
if (lean_obj_tag(v_pre_825_) == 0)
{
lean_object* v_str_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_str_826_ = lean_ctor_get(v_x_824_, 1);
v___x_827_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_828_ = lean_string_dec_eq(v_str_826_, v___x_827_);
if (v___x_828_ == 0)
{
return v___x_828_;
}
else
{
return v_suppressElabErrors_822_;
}
}
else
{
return v___y_823_;
}
}
else
{
return v___y_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_829_, lean_object* v___y_830_, lean_object* v_x_831_){
_start:
{
uint8_t v_suppressElabErrors_boxed_832_; uint8_t v___y_10919__boxed_833_; uint8_t v_res_834_; lean_object* v_r_835_; 
v_suppressElabErrors_boxed_832_ = lean_unbox(v_suppressElabErrors_829_);
v___y_10919__boxed_833_ = lean_unbox(v___y_830_);
v_res_834_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_832_, v___y_10919__boxed_833_, v_x_831_);
lean_dec(v_x_831_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_836_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_840_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
lean_ctor_set(v___x_842_, 4, v___x_840_);
lean_ctor_set(v___x_842_, 5, v___x_840_);
lean_ctor_set(v___x_842_, 6, v___x_840_);
lean_ctor_set(v___x_842_, 7, v___x_840_);
lean_ctor_set(v___x_842_, 8, v___x_840_);
lean_ctor_set(v___x_842_, 9, v___x_840_);
lean_ctor_set(v___x_842_, 10, v___x_840_);
lean_ctor_set(v___x_842_, 11, v___x_839_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_unsigned_to_nat(32u);
v___x_844_ = lean_mk_empty_array_with_capacity(v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_846_ = ((size_t)5ULL);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_unsigned_to_nat(32u);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3);
v___x_851_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
lean_ctor_set(v___x_851_, 2, v___x_847_);
lean_ctor_set(v___x_851_, 3, v___x_847_);
lean_ctor_set_usize(v___x_851_, 4, v___x_846_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = lean_box(1);
v___x_853_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4);
v___x_854_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
lean_ctor_set(v___x_855_, 2, v___x_852_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(lean_object* v_msgData_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v_env_860_; uint8_t v___x_861_; lean_object* v_env_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_scopes_865_; lean_object* v___x_866_; lean_object* v_opts_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_859_ = lean_st_ref_get(v___y_857_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v___x_861_ = 0;
v_env_862_ = l_Lean_Environment_setRecordingDeps(v_env_860_, v___x_861_);
v___x_863_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_864_ = lean_st_ref_get(v___y_857_);
v_scopes_865_ = lean_ctor_get(v___x_864_, 2);
lean_inc(v_scopes_865_);
lean_dec(v___x_864_);
v___x_866_ = l_List_head_x21___redArg(v___x_863_, v_scopes_865_);
lean_dec(v_scopes_865_);
v_opts_867_ = lean_ctor_get(v___x_866_, 1);
lean_inc_ref(v_opts_867_);
lean_dec(v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2);
v___x_869_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5);
v___x_870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_870_, 0, v_env_862_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
lean_ctor_set(v___x_870_, 2, v___x_869_);
lean_ctor_set(v___x_870_, 3, v_opts_867_);
v___x_871_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_msgData_856_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_msgData_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_873_, v___y_874_);
lean_dec(v___y_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(lean_object* v_ref_878_, lean_object* v_msgData_879_, uint8_t v_severity_880_, uint8_t v_isSilent_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; uint8_t v___y_892_; lean_object* v___y_893_; uint8_t v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; uint8_t v___y_954_; lean_object* v___y_955_; uint8_t v___y_979_; uint8_t v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; lean_object* v___y_983_; uint8_t v___y_987_; uint8_t v___y_988_; uint8_t v___y_989_; uint8_t v___x_1004_; uint8_t v___y_1006_; uint8_t v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1010_; uint8_t v___x_1022_; 
v___x_1004_ = 2;
v___x_1022_ = l_Lean_instBEqMessageSeverity_beq(v_severity_880_, v___x_1004_);
if (v___x_1022_ == 0)
{
v___y_1010_ = v___x_1022_;
goto v___jp_1009_;
}
else
{
uint8_t v___x_1023_; 
lean_inc_ref(v_msgData_879_);
v___x_1023_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_879_);
v___y_1010_ = v___x_1023_;
goto v___jp_1009_;
}
v___jp_885_:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Elab_Command_getScope___redArg(v___y_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_currNamespace_896_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v_currNamespace_896_ = lean_ctor_get(v_a_895_, 2);
lean_inc(v_currNamespace_896_);
lean_dec(v_a_895_);
v___x_897_ = l_Lean_Elab_Command_getScope___redArg(v___y_893_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_933_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_933_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_933_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_933_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_openDecls_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_env_907_; lean_object* v_messages_908_; lean_object* v_scopes_909_; lean_object* v_usedQuotCtxts_910_; lean_object* v_nextMacroScope_911_; lean_object* v_maxRecDepth_912_; lean_object* v_ngen_913_; lean_object* v_auxDeclNGen_914_; lean_object* v_infoState_915_; lean_object* v_traceState_916_; lean_object* v_snapshotTasks_917_; lean_object* v_prevLinterStates_918_; lean_object* v_codeQualityEntryTasks_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v_openDecls_902_ = lean_ctor_get(v_a_898_, 3);
lean_inc(v_openDecls_902_);
lean_dec(v_a_898_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_currNamespace_896_);
lean_ctor_set(v___x_903_, 1, v_openDecls_902_);
v___x_904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___y_889_);
lean_inc_ref(v___y_886_);
lean_inc_ref(v___y_890_);
v___x_905_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_905_, 0, v___y_890_);
lean_ctor_set(v___x_905_, 1, v___y_891_);
lean_ctor_set(v___x_905_, 2, v___y_888_);
lean_ctor_set(v___x_905_, 3, v___y_886_);
lean_ctor_set(v___x_905_, 4, v___x_904_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*5, v___y_887_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*5 + 1, v___y_892_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*5 + 2, v_isSilent_881_);
v___x_906_ = lean_st_ref_take(v___y_893_);
v_env_907_ = lean_ctor_get(v___x_906_, 0);
v_messages_908_ = lean_ctor_get(v___x_906_, 1);
v_scopes_909_ = lean_ctor_get(v___x_906_, 2);
v_usedQuotCtxts_910_ = lean_ctor_get(v___x_906_, 3);
v_nextMacroScope_911_ = lean_ctor_get(v___x_906_, 4);
v_maxRecDepth_912_ = lean_ctor_get(v___x_906_, 5);
v_ngen_913_ = lean_ctor_get(v___x_906_, 6);
v_auxDeclNGen_914_ = lean_ctor_get(v___x_906_, 7);
v_infoState_915_ = lean_ctor_get(v___x_906_, 8);
v_traceState_916_ = lean_ctor_get(v___x_906_, 9);
v_snapshotTasks_917_ = lean_ctor_get(v___x_906_, 10);
v_prevLinterStates_918_ = lean_ctor_get(v___x_906_, 11);
v_codeQualityEntryTasks_919_ = lean_ctor_get(v___x_906_, 12);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v___x_906_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_codeQualityEntryTasks_919_);
lean_inc(v_prevLinterStates_918_);
lean_inc(v_snapshotTasks_917_);
lean_inc(v_traceState_916_);
lean_inc(v_infoState_915_);
lean_inc(v_auxDeclNGen_914_);
lean_inc(v_ngen_913_);
lean_inc(v_maxRecDepth_912_);
lean_inc(v_nextMacroScope_911_);
lean_inc(v_usedQuotCtxts_910_);
lean_inc(v_scopes_909_);
lean_inc(v_messages_908_);
lean_inc(v_env_907_);
lean_dec(v___x_906_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_MessageLog_add(v___x_905_, v_messages_908_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_env_907_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_scopes_909_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_usedQuotCtxts_910_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_nextMacroScope_911_);
lean_ctor_set(v_reuseFailAlloc_931_, 5, v_maxRecDepth_912_);
lean_ctor_set(v_reuseFailAlloc_931_, 6, v_ngen_913_);
lean_ctor_set(v_reuseFailAlloc_931_, 7, v_auxDeclNGen_914_);
lean_ctor_set(v_reuseFailAlloc_931_, 8, v_infoState_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 9, v_traceState_916_);
lean_ctor_set(v_reuseFailAlloc_931_, 10, v_snapshotTasks_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 11, v_prevLinterStates_918_);
lean_ctor_set(v_reuseFailAlloc_931_, 12, v_codeQualityEntryTasks_919_);
v___x_926_ = v_reuseFailAlloc_931_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_st_ref_put(v___y_893_, v___x_926_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_923_);
v___x_929_ = v___x_900_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_923_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_currNamespace_896_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
v_a_934_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_897_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_897_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
v_a_942_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_894_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_894_);
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
v___jp_950_:
{
lean_object* v_fileName_956_; lean_object* v_fileMap_957_; uint8_t v_suppressElabErrors_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_977_; 
v_fileName_956_ = lean_ctor_get(v___y_882_, 0);
v_fileMap_957_ = lean_ctor_get(v___y_882_, 1);
v_suppressElabErrors_958_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*10);
v___x_959_ = lean_box(v_suppressElabErrors_958_);
v___x_960_ = lean_box(v___y_951_);
v___f_961_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_961_, 0, v___x_959_);
lean_closure_set(v___f_961_, 1, v___x_960_);
v___x_962_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_879_);
v___x_963_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_962_, v___y_883_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_977_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_977_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_977_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc_ref_n(v_fileMap_957_, 2);
v___x_968_ = l_Lean_FileMap_toPosition(v_fileMap_957_, v___y_952_);
lean_dec(v___y_952_);
v___x_969_ = l_Lean_FileMap_toPosition(v_fileMap_957_, v___y_955_);
lean_dec(v___y_955_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_958_ == 0)
{
lean_del_object(v___x_966_);
lean_dec_ref(v___f_961_);
v___y_886_ = v___x_971_;
v___y_887_ = v___y_953_;
v___y_888_ = v___x_970_;
v___y_889_ = v_a_964_;
v___y_890_ = v_fileName_956_;
v___y_891_ = v___x_968_;
v___y_892_ = v___y_954_;
v___y_893_ = v___y_883_;
goto v___jp_885_;
}
else
{
uint8_t v___x_972_; 
lean_inc(v_a_964_);
v___x_972_ = l_Lean_MessageData_hasTag(v___f_961_, v_a_964_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec_ref_known(v___x_970_, 1);
lean_dec_ref(v___x_968_);
lean_dec(v_a_964_);
v___x_973_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_973_);
v___x_975_ = v___x_966_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_del_object(v___x_966_);
v___y_886_ = v___x_971_;
v___y_887_ = v___y_953_;
v___y_888_ = v___x_970_;
v___y_889_ = v_a_964_;
v___y_890_ = v_fileName_956_;
v___y_891_ = v___x_968_;
v___y_892_ = v___y_954_;
v___y_893_ = v___y_883_;
goto v___jp_885_;
}
}
}
}
v___jp_978_:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Syntax_getTailPos_x3f(v___y_981_, v___y_980_);
lean_dec(v___y_981_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_inc(v___y_983_);
v___y_951_ = v___y_979_;
v___y_952_ = v___y_983_;
v___y_953_ = v___y_980_;
v___y_954_ = v___y_982_;
v___y_955_ = v___y_983_;
goto v___jp_950_;
}
else
{
lean_object* v_val_985_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v___x_984_, 1);
v___y_951_ = v___y_979_;
v___y_952_ = v___y_983_;
v___y_953_ = v___y_980_;
v___y_954_ = v___y_982_;
v___y_955_ = v_val_985_;
goto v___jp_950_;
}
}
v___jp_986_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Elab_Command_getRef___redArg(v___y_882_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_ref_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v_ref_992_ = l_Lean_replaceRef(v_ref_878_, v_a_991_);
lean_dec(v_a_991_);
v___x_993_ = l_Lean_Syntax_getPos_x3f(v_ref_992_, v___y_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___y_979_ = v___y_987_;
v___y_980_ = v___y_988_;
v___y_981_ = v_ref_992_;
v___y_982_ = v___y_989_;
v___y_983_ = v___x_994_;
goto v___jp_978_;
}
else
{
lean_object* v_val_995_; 
v_val_995_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_993_, 1);
v___y_979_ = v___y_987_;
v___y_980_ = v___y_988_;
v___y_981_ = v_ref_992_;
v___y_982_ = v___y_989_;
v___y_983_ = v_val_995_;
goto v___jp_978_;
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_msgData_879_);
v_a_996_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_990_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_990_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
v___jp_1005_:
{
if (v___y_1008_ == 0)
{
v___y_987_ = v___y_1006_;
v___y_988_ = v___y_1007_;
v___y_989_ = v_severity_880_;
goto v___jp_986_;
}
else
{
v___y_987_ = v___y_1006_;
v___y_988_ = v___y_1007_;
v___y_989_ = v___x_1004_;
goto v___jp_986_;
}
}
v___jp_1009_:
{
if (v___y_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_scopes_1013_; lean_object* v___x_1014_; lean_object* v_opts_1015_; uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1011_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1012_ = lean_st_ref_get(v___y_883_);
v_scopes_1013_ = lean_ctor_get(v___x_1012_, 2);
lean_inc(v_scopes_1013_);
lean_dec(v___x_1012_);
v___x_1014_ = l_List_head_x21___redArg(v___x_1011_, v_scopes_1013_);
lean_dec(v_scopes_1013_);
v_opts_1015_ = lean_ctor_get(v___x_1014_, 1);
lean_inc_ref(v_opts_1015_);
lean_dec(v___x_1014_);
v___x_1016_ = 1;
v___x_1017_ = l_Lean_instBEqMessageSeverity_beq(v_severity_880_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v_opts_1015_);
v___y_1006_ = v___y_1010_;
v___y_1007_ = v___y_1010_;
v___y_1008_ = v___x_1017_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = l_Lean_warningAsError;
v___x_1019_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_1015_, v___x_1018_);
lean_dec_ref(v_opts_1015_);
v___y_1006_ = v___y_1010_;
v___y_1007_ = v___y_1010_;
v___y_1008_ = v___x_1019_;
goto v___jp_1005_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref(v_msgData_879_);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1024_, lean_object* v_msgData_1025_, lean_object* v_severity_1026_, lean_object* v_isSilent_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_severity_boxed_1031_; uint8_t v_isSilent_boxed_1032_; lean_object* v_res_1033_; 
v_severity_boxed_1031_ = lean_unbox(v_severity_1026_);
v_isSilent_boxed_1032_ = lean_unbox(v_isSilent_1027_);
v_res_1033_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1024_, v_msgData_1025_, v_severity_boxed_1031_, v_isSilent_boxed_1032_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v_ref_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(lean_object* v_ref_1034_, lean_object* v_msgData_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = 1;
v___x_1040_ = 0;
v___x_1041_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_1034_, v_msgData_1035_, v___x_1039_, v___x_1040_, v___y_1036_, v___y_1037_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(lean_object* v_ref_1042_, lean_object* v_msgData_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_1042_, v_msgData_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v_ref_1042_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(lean_object* v_linterOption_1054_, lean_object* v_stx_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_name_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1078_; 
v_name_1060_ = lean_ctor_get(v_linterOption_1054_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_linterOption_1054_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_linterOption_1054_, 1);
lean_dec(v_unused_1079_);
v___x_1062_ = v_linterOption_1054_;
v_isShared_1063_ = v_isSharedCheck_1078_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_name_1060_);
lean_dec(v_linterOption_1054_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1078_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
lean_inc(v_name_1060_);
v___x_1065_ = l_Lean_MessageData_ofName(v_name_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 7);
lean_ctor_set(v___x_1062_, 1, v___x_1065_);
lean_ctor_set(v___x_1062_, 0, v___x_1064_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_disable_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1068_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v_disable_1070_ = l_Lean_MessageData_note(v___x_1069_);
v___x_1071_ = l_Lean_Linter_linterMessageTag;
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_msg_1056_);
lean_ctor_set(v___x_1072_, 1, v_disable_1070_);
v___x_1073_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_name_1060_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
lean_inc(v_stx_1055_);
v___x_1075_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_stx_1055_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_1055_, v___x_1075_, v___y_1057_, v___y_1058_);
lean_dec(v_stx_1055_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(lean_object* v_linterOption_1080_, lean_object* v_stx_1081_, lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v_linterOption_1080_, v_stx_1081_, v_msg_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
return v___x_1089_;
}
else
{
lean_object* v_head_1090_; lean_object* v_tail_1091_; uint8_t v___x_1092_; 
v_head_1090_ = lean_ctor_get(v_x_1088_, 0);
v_tail_1091_ = lean_ctor_get(v_x_1088_, 1);
v___x_1092_ = lean_string_dec_eq(v_a_1087_, v_head_1090_);
if (v___x_1092_ == 0)
{
v_x_1088_ = v_tail_1091_;
goto _start;
}
else
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(lean_object* v_a_1094_, lean_object* v_x_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_1094_, v_x_1095_);
lean_dec(v_x_1095_);
lean_dec_ref(v_a_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(lean_object* v_as_x27_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
if (lean_obj_tag(v_as_x27_1101_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1102_);
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1111_; 
v_head_1107_ = lean_ctor_get(v_as_x27_1101_, 0);
v_tail_1108_ = lean_ctor_get(v_as_x27_1101_, 1);
v_fst_1109_ = lean_ctor_get(v_head_1107_, 0);
v_snd_1110_ = lean_ctor_get(v_head_1107_, 1);
v___x_1111_ = lean_box(0);
if (lean_obj_tag(v_snd_1110_) == 1)
{
lean_object* v_str_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_str_1112_ = lean_ctor_get(v_snd_1110_, 1);
v___x_1113_ = ((lean_object*)(l_Lean_Linter_List_allowedWidths));
lean_inc_ref(v_str_1112_);
v___x_1114_ = l_Lean_Linter_List_stripBinderName(v_str_1112_);
v___x_1115_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1114_, v___x_1113_);
lean_dec_ref(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1116_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1117_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
lean_inc_ref(v_str_1112_);
v___x_1118_ = l_Lean_stringToMessageData(v_str_1112_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
lean_inc(v_fst_1109_);
v___x_1120_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1116_, v_fst_1109_, v___x_1119_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref_known(v___x_1120_, 1);
v_as_x27_1101_ = v_tail_1108_;
v_b_1102_ = v___x_1111_;
goto _start;
}
else
{
return v___x_1120_;
}
}
else
{
v_as_x27_1101_ = v_tail_1108_;
v_b_1102_ = v___x_1111_;
goto _start;
}
}
else
{
v_as_x27_1101_ = v_tail_1108_;
v_b_1102_ = v___x_1111_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(lean_object* v_as_x27_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1124_, v_b_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_as_x27_1124_);
return v_res_1129_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(lean_object* v_as_x27_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
if (lean_obj_tag(v_as_x27_1133_) == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_b_1134_);
return v___x_1138_;
}
else
{
lean_object* v_head_1139_; lean_object* v_tail_1140_; lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1143_; 
v_head_1139_ = lean_ctor_get(v_as_x27_1133_, 0);
v_tail_1140_ = lean_ctor_get(v_as_x27_1133_, 1);
v_fst_1141_ = lean_ctor_get(v_head_1139_, 0);
v_snd_1142_ = lean_ctor_get(v_head_1139_, 1);
v___x_1143_ = lean_box(0);
if (lean_obj_tag(v_snd_1142_) == 1)
{
lean_object* v_str_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_str_1144_ = lean_ctor_get(v_snd_1142_, 1);
v___x_1145_ = ((lean_object*)(l_Lean_Linter_List_allowedBitVecWidths));
lean_inc_ref(v_str_1144_);
v___x_1146_ = l_Lean_Linter_List_stripBinderName(v_str_1144_);
v___x_1147_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1146_, v___x_1145_);
lean_dec_ref(v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1148_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1149_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
lean_inc_ref(v_str_1144_);
v___x_1150_ = l_Lean_stringToMessageData(v_str_1144_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
lean_inc(v_fst_1141_);
v___x_1152_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1148_, v_fst_1141_, v___x_1151_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_dec_ref_known(v___x_1152_, 1);
v_as_x27_1133_ = v_tail_1140_;
v_b_1134_ = v___x_1143_;
goto _start;
}
else
{
return v___x_1152_;
}
}
else
{
v_as_x27_1133_ = v_tail_1140_;
v_b_1134_ = v___x_1143_;
goto _start;
}
}
else
{
v_as_x27_1133_ = v_tail_1140_;
v_b_1134_ = v___x_1143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(lean_object* v_as_x27_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1156_, v_b_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v_as_x27_1156_);
return v_res_1161_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(lean_object* v_as_x27_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
if (lean_obj_tag(v_as_x27_1165_) == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_b_1166_);
return v___x_1170_;
}
else
{
lean_object* v_head_1171_; lean_object* v_tail_1172_; lean_object* v_fst_1173_; lean_object* v_snd_1174_; lean_object* v___x_1175_; 
v_head_1171_ = lean_ctor_get(v_as_x27_1165_, 0);
v_tail_1172_ = lean_ctor_get(v_as_x27_1165_, 1);
v_fst_1173_ = lean_ctor_get(v_head_1171_, 0);
v_snd_1174_ = lean_ctor_get(v_head_1171_, 1);
v___x_1175_ = lean_box(0);
if (lean_obj_tag(v_snd_1174_) == 1)
{
lean_object* v_str_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_str_1176_ = lean_ctor_get(v_snd_1174_, 1);
v___x_1177_ = ((lean_object*)(l_Lean_Linter_List_allowedIndices));
lean_inc_ref(v_str_1176_);
v___x_1178_ = l_Lean_Linter_List_stripBinderName(v_str_1176_);
v___x_1179_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_1178_, v___x_1177_);
lean_dec_ref(v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1180_ = l_Lean_Linter_List_linter_indexVariables;
v___x_1181_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
lean_inc_ref(v_str_1176_);
v___x_1182_ = l_Lean_stringToMessageData(v_str_1176_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
lean_inc(v_fst_1173_);
v___x_1184_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_1180_, v_fst_1173_, v___x_1183_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref_known(v___x_1184_, 1);
v_as_x27_1165_ = v_tail_1172_;
v_b_1166_ = v___x_1175_;
goto _start;
}
else
{
return v___x_1184_;
}
}
else
{
v_as_x27_1165_ = v_tail_1172_;
v_b_1166_ = v___x_1175_;
goto _start;
}
}
else
{
v_as_x27_1165_ = v_tail_1172_;
v_b_1166_ = v___x_1175_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(lean_object* v_as_x27_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1188_, v_b_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v_as_x27_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_b_1200_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_b_1200_);
v___x_1206_ = lean_box(0);
v_a_1207_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
lean_inc(v_a_1207_);
v___x_1208_ = l_Lean_Linter_List_numericalIndices(v_a_1207_);
v___x_1209_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1208_, v___x_1206_, v___y_1201_, v___y_1202_);
lean_dec(v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1209_, 1);
lean_inc(v_a_1207_);
v___x_1210_ = l_Lean_Linter_List_numericalWidths(v_a_1207_);
v___x_1211_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1210_, v___x_1206_, v___y_1201_, v___y_1202_);
lean_dec(v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref_known(v___x_1211_, 1);
lean_inc(v_a_1207_);
v___x_1212_ = l_Lean_Linter_List_bitVecWidths(v_a_1207_);
v___x_1213_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1212_, v___x_1206_, v___y_1201_, v___y_1202_);
lean_dec(v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; 
lean_dec_ref_known(v___x_1213_, 1);
v___x_1214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1199_, v___x_1215_);
v_i_1199_ = v___x_1216_;
v_b_1200_ = v___x_1214_;
goto _start;
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_a_1218_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1213_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1211_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1211_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1209_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1209_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(lean_object* v_as_1242_, lean_object* v_sz_1243_, lean_object* v_i_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1243_);
lean_dec(v_sz_1243_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1244_);
lean_dec(v_i_1244_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1242_, v_sz_boxed_1249_, v_i_boxed_1250_, v_b_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_as_1242_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(lean_object* v_as_1252_, size_t v_sz_1253_, size_t v_i_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_usize_dec_lt(v_i_1254_, v_sz_1253_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_b_1255_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v_b_1255_);
v___x_1261_ = lean_box(0);
v_a_1262_ = lean_array_uget_borrowed(v_as_1252_, v_i_1254_);
lean_inc(v_a_1262_);
v___x_1263_ = l_Lean_Linter_List_numericalIndices(v_a_1262_);
v___x_1264_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1263_, v___x_1261_, v___y_1256_, v___y_1257_);
lean_dec(v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref_known(v___x_1264_, 1);
lean_inc(v_a_1262_);
v___x_1265_ = l_Lean_Linter_List_numericalWidths(v_a_1262_);
v___x_1266_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1265_, v___x_1261_, v___y_1256_, v___y_1257_);
lean_dec(v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1266_, 1);
lean_inc(v_a_1262_);
v___x_1267_ = l_Lean_Linter_List_bitVecWidths(v_a_1262_);
v___x_1268_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1267_, v___x_1261_, v___y_1256_, v___y_1257_);
lean_dec(v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref_known(v___x_1268_, 1);
v___x_1269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1254_, v___x_1270_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_1252_, v_sz_1253_, v___x_1271_, v___x_1269_, v___y_1256_, v___y_1257_);
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1268_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1268_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1266_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1266_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1264_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1264_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_as_1297_, lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_1297_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v_as_1297_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(lean_object* v_init_1307_, lean_object* v_n_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
if (lean_obj_tag(v_n_1308_) == 0)
{
lean_object* v_cs_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; size_t v_sz_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_cs_1313_ = lean_ctor_get(v_n_1308_, 0);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_b_1309_);
v_sz_1316_ = lean_array_size(v_cs_1313_);
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1307_, v_cs_1313_, v_sz_1316_, v___x_1317_, v___x_1315_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1333_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v_a_1319_, 0);
if (lean_obj_tag(v_fst_1323_) == 0)
{
lean_object* v_snd_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_snd_1324_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v_snd_1324_);
lean_dec(v_a_1319_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_snd_1324_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1325_);
v___x_1327_ = v___x_1321_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v_val_1329_; lean_object* v___x_1331_; 
lean_inc_ref(v_fst_1323_);
lean_dec(v_a_1319_);
v_val_1329_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v_fst_1323_, 1);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v_val_1329_);
v___x_1331_ = v___x_1321_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_val_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1334_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1318_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1318_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_vs_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_vs_1342_ = lean_ctor_get(v_n_1308_, 0);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_b_1309_);
v_sz_1345_ = lean_array_size(v_vs_1342_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_1342_, v_sz_1345_, v___x_1346_, v___x_1344_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1362_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1362_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1362_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_fst_1352_; 
v_fst_1352_ = lean_ctor_get(v_a_1348_, 0);
if (lean_obj_tag(v_fst_1352_) == 0)
{
lean_object* v_snd_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v_snd_1353_ = lean_ctor_get(v_a_1348_, 1);
lean_inc(v_snd_1353_);
lean_dec(v_a_1348_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_snd_1353_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1360_; 
lean_inc_ref(v_fst_1352_);
lean_dec(v_a_1348_);
v_val_1358_ = lean_ctor_get(v_fst_1352_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v_fst_1352_, 1);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_val_1358_);
v___x_1360_ = v___x_1350_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_val_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1347_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1347_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(lean_object* v_init_1371_, lean_object* v_as_1372_, size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_usize_dec_lt(v_i_1374_, v_sz_1373_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_b_1375_);
return v___x_1380_;
}
else
{
lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1415_; 
v_snd_1381_ = lean_ctor_get(v_b_1375_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_b_1375_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_b_1375_, 0);
lean_dec(v_unused_1416_);
v___x_1383_ = v_b_1375_;
v_isShared_1384_ = v_isSharedCheck_1415_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_dec(v_b_1375_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1415_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v_a_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_box(0);
v_a_1386_ = lean_array_uget_borrowed(v_as_1372_, v_i_1374_);
lean_inc(v_snd_1381_);
v___x_1387_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1371_, v_a_1386_, v_snd_1381_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1406_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1406_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1406_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
if (lean_obj_tag(v_a_1388_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1388_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1392_);
v___x_1394_ = v___x_1383_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_snd_1381_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; 
lean_del_object(v___x_1390_);
lean_dec(v_snd_1381_);
v_a_1399_ = lean_ctor_get(v_a_1388_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v_a_1388_, 1);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_a_1399_);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1401_ = v___x_1383_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_a_1399_);
v___x_1401_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
size_t v___x_1402_; size_t v___x_1403_; 
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = lean_usize_add(v_i_1374_, v___x_1402_);
v_i_1374_ = v___x_1403_;
v_b_1375_ = v___x_1401_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1383_);
lean_dec(v_snd_1381_);
v_a_1407_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1387_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1387_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(lean_object* v_init_1417_, lean_object* v_as_1418_, lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
size_t v_sz_boxed_1425_; size_t v_i_boxed_1426_; lean_object* v_res_1427_; 
v_sz_boxed_1425_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1426_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_1417_, v_as_1418_, v_sz_boxed_1425_, v_i_boxed_1426_, v_b_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_as_1418_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(lean_object* v_init_1428_, lean_object* v_n_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1428_, v_n_1429_, v_b_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_n_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(lean_object* v_as_1438_, size_t v_sz_1439_, size_t v_i_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1440_, v_sz_1439_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1441_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v_b_1441_);
v___x_1447_ = lean_box(0);
v_a_1448_ = lean_array_uget_borrowed(v_as_1438_, v_i_1440_);
lean_inc(v_a_1448_);
v___x_1449_ = l_Lean_Linter_List_numericalIndices(v_a_1448_);
v___x_1450_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1449_, v___x_1447_, v___y_1442_, v___y_1443_);
lean_dec(v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref_known(v___x_1450_, 1);
lean_inc(v_a_1448_);
v___x_1451_ = l_Lean_Linter_List_numericalWidths(v_a_1448_);
v___x_1452_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1451_, v___x_1447_, v___y_1442_, v___y_1443_);
lean_dec(v___x_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec_ref_known(v___x_1452_, 1);
lean_inc(v_a_1448_);
v___x_1453_ = l_Lean_Linter_List_bitVecWidths(v_a_1448_);
v___x_1454_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1453_, v___x_1447_, v___y_1442_, v___y_1443_);
lean_dec(v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
lean_dec_ref_known(v___x_1454_, 1);
v___x_1455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1440_, v___x_1456_);
v_i_1440_ = v___x_1457_;
v_b_1441_ = v___x_1455_;
goto _start;
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1454_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1454_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1452_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1452_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1450_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1450_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(lean_object* v_as_1483_, lean_object* v_sz_1484_, lean_object* v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1484_);
lean_dec(v_sz_1484_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1483_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_as_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1496_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_b_1496_);
v___x_1502_ = lean_box(0);
v_a_1503_ = lean_array_uget_borrowed(v_as_1493_, v_i_1495_);
lean_inc(v_a_1503_);
v___x_1504_ = l_Lean_Linter_List_numericalIndices(v_a_1503_);
v___x_1505_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_1504_, v___x_1502_, v___y_1497_, v___y_1498_);
lean_dec(v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref_known(v___x_1505_, 1);
lean_inc(v_a_1503_);
v___x_1506_ = l_Lean_Linter_List_numericalWidths(v_a_1503_);
v___x_1507_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_1506_, v___x_1502_, v___y_1497_, v___y_1498_);
lean_dec(v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref_known(v___x_1507_, 1);
lean_inc(v_a_1503_);
v___x_1508_ = l_Lean_Linter_List_bitVecWidths(v_a_1503_);
v___x_1509_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_1508_, v___x_1502_, v___y_1497_, v___y_1498_);
lean_dec(v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1509_, 1);
v___x_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1495_, v___x_1511_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_1493_, v_sz_1494_, v___x_1512_, v___x_1510_, v___y_1497_, v___y_1498_);
return v___x_1513_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1509_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1509_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1522_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1507_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1507_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1505_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1505_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(lean_object* v_as_1538_, lean_object* v_sz_1539_, lean_object* v_i_1540_, lean_object* v_b_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1539_);
lean_dec(v_sz_1539_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_1538_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec_ref(v_as_1538_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(lean_object* v_t_1548_, lean_object* v_init_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_root_1553_; lean_object* v_tail_1554_; lean_object* v___x_1555_; 
v_root_1553_ = lean_ctor_get(v_t_1548_, 0);
v_tail_1554_ = lean_ctor_get(v_t_1548_, 1);
v___x_1555_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_1549_, v_root_1553_, v_init_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1592_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1592_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1592_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
if (lean_obj_tag(v_a_1556_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; 
v_a_1560_ = lean_ctor_get(v_a_1556_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v_a_1556_, 1);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v_a_1560_);
v___x_1562_ = v___x_1558_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
lean_del_object(v___x_1558_);
v_a_1564_ = lean_ctor_get(v_a_1556_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v_a_1556_, 1);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1564_);
v_sz_1567_ = lean_array_size(v_tail_1554_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_1554_, v_sz_1567_, v___x_1568_, v___x_1566_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1583_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1583_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1583_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_fst_1574_; 
v_fst_1574_ = lean_ctor_get(v_a_1570_, 0);
if (lean_obj_tag(v_fst_1574_) == 0)
{
lean_object* v_snd_1575_; lean_object* v___x_1577_; 
v_snd_1575_ = lean_ctor_get(v_a_1570_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_snd_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_snd_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
lean_object* v_val_1579_; lean_object* v___x_1581_; 
lean_inc_ref(v_fst_1574_);
lean_dec(v_a_1570_);
v_val_1579_ = lean_ctor_get(v_fst_1574_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_fst_1574_, 1);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_val_1579_);
v___x_1581_ = v___x_1572_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_val_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1569_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1569_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1555_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1555_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(lean_object* v_t_1601_, lean_object* v_init_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_t_1601_, v_init_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_t_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0(lean_object* v_stx_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_scopes_1616_; lean_object* v___x_1617_; lean_object* v_opts_1618_; lean_object* v___x_1619_; lean_object* v_name_1620_; lean_object* v_map_1621_; lean_object* v___x_1622_; 
v___x_1611_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1612_ = lean_st_ref_get(v___y_1609_);
v_scopes_1616_ = lean_ctor_get(v___x_1612_, 2);
lean_inc(v_scopes_1616_);
lean_dec(v___x_1612_);
v___x_1617_ = l_List_head_x21___redArg(v___x_1611_, v_scopes_1616_);
lean_dec(v_scopes_1616_);
v_opts_1618_ = lean_ctor_get(v___x_1617_, 1);
lean_inc_ref(v_opts_1618_);
lean_dec(v___x_1617_);
v___x_1619_ = l_Lean_Linter_List_linter_indexVariables;
v_name_1620_ = lean_ctor_get(v___x_1619_, 0);
v_map_1621_ = lean_ctor_get(v_opts_1618_, 0);
lean_inc(v_map_1621_);
lean_dec_ref(v_opts_1618_);
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1621_, v_name_1620_);
lean_dec(v_map_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
goto v___jp_1613_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1655_; 
v_val_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1655_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_val_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1655_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
if (lean_obj_tag(v_val_1623_) == 1)
{
uint8_t v_v_1627_; 
v_v_1627_ = lean_ctor_get_uint8(v_val_1623_, 0);
lean_dec_ref_known(v_val_1623_, 0);
if (v_v_1627_ == 0)
{
lean_del_object(v___x_1625_);
goto v___jp_1613_;
}
else
{
lean_object* v___x_1628_; lean_object* v_messages_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_st_ref_get(v___y_1609_);
v_messages_1629_ = lean_ctor_get(v___x_1628_, 1);
lean_inc_ref(v_messages_1629_);
lean_dec(v___x_1628_);
v___x_1630_ = l_Lean_MessageLog_hasErrors(v_messages_1629_);
lean_dec_ref(v_messages_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v_infoState_1637_; uint8_t v_enabled_1638_; 
v___x_1631_ = lean_st_ref_get(v___y_1609_);
v_infoState_1637_ = lean_ctor_get(v___x_1631_, 8);
lean_inc_ref(v_infoState_1637_);
lean_dec(v___x_1631_);
v_enabled_1638_ = lean_ctor_get_uint8(v_infoState_1637_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1637_);
if (v_enabled_1638_ == 0)
{
goto v___jp_1632_;
}
else
{
if (v___x_1630_ == 0)
{
lean_object* v___x_1639_; lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_del_object(v___x_1625_);
v___x_1639_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_1609_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_1640_, v___x_1641_, v___y_1608_, v___y_1609_);
lean_dec(v_a_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1650_);
v___x_1644_ = v___x_1642_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v___x_1642_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1641_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1641_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
return v___x_1642_;
}
}
else
{
goto v___jp_1632_;
}
}
v___jp_1632_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_box(0);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_box(0);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1651_);
v___x_1653_ = v___x_1625_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
goto v___jp_1613_;
}
}
}
v___jp_1613_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_indexLinter___lam__0___boxed(lean_object* v_stx_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_stx_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(lean_object* v_as_1674_, lean_object* v_as_x27_1675_, lean_object* v_b_1676_, lean_object* v_a_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v_as_x27_1675_, v_b_1676_, v___y_1678_, v___y_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(lean_object* v_as_1682_, lean_object* v_as_x27_1683_, lean_object* v_b_1684_, lean_object* v_a_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(v_as_1682_, v_as_x27_1683_, v_b_1684_, v_a_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_as_x27_1683_);
lean_dec(v_as_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(lean_object* v_as_1690_, lean_object* v_as_x27_1691_, lean_object* v_b_1692_, lean_object* v_a_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v_as_x27_1691_, v_b_1692_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(lean_object* v_as_1698_, lean_object* v_as_x27_1699_, lean_object* v_b_1700_, lean_object* v_a_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(v_as_1698_, v_as_x27_1699_, v_b_1700_, v_a_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v_as_x27_1699_);
lean_dec(v_as_1698_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(lean_object* v_as_1706_, lean_object* v_as_x27_1707_, lean_object* v_b_1708_, lean_object* v_a_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v_as_x27_1707_, v_b_1708_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(lean_object* v_as_1714_, lean_object* v_as_x27_1715_, lean_object* v_b_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(v_as_1714_, v_as_x27_1715_, v_b_1716_, v_a_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v_as_x27_1715_);
lean_dec(v_as_1714_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(lean_object* v_msgData_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_1722_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_msgData_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_Linter_List_indexLinter));
v___x_1734_ = l_Lean_Elab_Command_addLinter(v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(lean_object* v_e_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Expr_hasMVar(v_e_1795_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_e_1795_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v_mctx_1801_; lean_object* v___x_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1805_; lean_object* v_cache_1806_; lean_object* v_zetaDeltaFVarIds_1807_; lean_object* v_postponed_1808_; lean_object* v_diag_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v___x_1800_ = lean_st_ref_get(v___y_1796_);
v_mctx_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_mctx_1801_);
lean_dec(v___x_1800_);
v___x_1802_ = l_Lean_instantiateMVarsCore(v_mctx_1801_, v_e_1795_);
v_fst_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_fst_1803_);
v_snd_1804_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1802_);
v___x_1805_ = lean_st_ref_take(v___y_1796_);
v_cache_1806_ = lean_ctor_get(v___x_1805_, 1);
v_zetaDeltaFVarIds_1807_ = lean_ctor_get(v___x_1805_, 2);
v_postponed_1808_ = lean_ctor_get(v___x_1805_, 3);
v_diag_1809_ = lean_ctor_get(v___x_1805_, 4);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1805_, 0);
lean_dec(v_unused_1819_);
v___x_1811_ = v___x_1805_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_diag_1809_);
lean_inc(v_postponed_1808_);
lean_inc(v_zetaDeltaFVarIds_1807_);
lean_inc(v_cache_1806_);
lean_dec(v___x_1805_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_snd_1804_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_snd_1804_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_cache_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_zetaDeltaFVarIds_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_postponed_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_diag_1809_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_put(v___y_1796_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_fst_1803_);
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(lean_object* v_e_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1820_, v___y_1821_);
lean_dec(v___y_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(lean_object* v_e_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_e_1824_, v___y_1826_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(v_e_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_Linter_List_binders___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = ((lean_object*)(l_Lean_Linter_List_binders___lam__0___closed__1));
v___x_1843_ = l_Lean_Expr_const___override(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0(lean_object* v_expr_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___y_1851_; lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Meta_saveState___redArg(v___y_1846_, v___y_1848_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
lean_inc(v___y_1848_);
lean_inc(v___y_1846_);
v___x_1856_ = lean_infer_type(v_expr_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_dec(v_a_1855_);
lean_dec(v___y_1848_);
v___y_1851_ = v___x_1856_;
goto v___jp_1850_;
}
else
{
lean_object* v_a_1857_; uint8_t v___y_1859_; uint8_t v___x_1871_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v___x_1871_ = l_Lean_Exception_isInterrupt(v_a_1857_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; 
lean_inc(v_a_1857_);
v___x_1872_ = l_Lean_Exception_isRuntime(v_a_1857_);
v___y_1859_ = v___x_1872_;
goto v___jp_1858_;
}
else
{
v___y_1859_ = v___x_1871_;
goto v___jp_1858_;
}
v___jp_1858_:
{
if (v___y_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1856_, 1);
v___x_1860_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1855_, v___y_1846_, v___y_1848_);
lean_dec(v___y_1848_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1860_, 1);
v___x_1861_ = lean_obj_once(&l_Lean_Linter_List_binders___lam__0___closed__2, &l_Lean_Linter_List_binders___lam__0___closed__2_once, _init_l_Lean_Linter_List_binders___lam__0___closed__2);
v___x_1862_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_1861_, v___y_1846_);
lean_dec(v___y_1846_);
return v___x_1862_;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v___y_1846_);
v_a_1863_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1860_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1860_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_dec(v_a_1855_);
lean_dec(v___y_1848_);
v___y_1851_ = v___x_1856_;
goto v___jp_1850_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_expr_1844_);
v_a_1873_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1854_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1854_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
v___jp_1850_:
{
if (lean_obj_tag(v___y_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___y_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___y_1851_, 1);
v___x_1853_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v_a_1852_, v___y_1846_);
lean_dec(v___y_1846_);
return v___x_1853_;
}
else
{
lean_dec(v___y_1846_);
return v___y_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__0___boxed(lean_object* v_expr_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Linter_List_binders___lam__0(v_expr_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1(lean_object* v_p_1888_, lean_object* v_ctx_1889_, lean_object* v_ti_1890_){
_start:
{
uint8_t v_isBinder_1892_; 
v_isBinder_1892_ = lean_ctor_get_uint8(v_ti_1890_, sizeof(void*)*4);
if (v_isBinder_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_ti_1890_);
lean_dec_ref(v_ctx_1889_);
lean_dec_ref(v_p_1888_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v_toElabInfo_1895_; lean_object* v_lctx_1896_; lean_object* v_expr_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v_toElabInfo_1895_ = lean_ctor_get(v_ti_1890_, 0);
lean_inc_ref(v_toElabInfo_1895_);
v_lctx_1896_ = lean_ctor_get(v_ti_1890_, 1);
lean_inc_ref_n(v_lctx_1896_, 2);
v_expr_1897_ = lean_ctor_get(v_ti_1890_, 3);
lean_inc_ref_n(v_expr_1897_, 2);
lean_dec_ref(v_ti_1890_);
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1898_, 0, v_expr_1897_);
v___x_1899_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1889_, v_lctx_1896_, v___f_1898_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1943_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1943_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1943_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
lean_inc(v_a_1900_);
v___x_1904_ = l_Lean_Expr_cleanupAnnotations(v_a_1900_);
v___x_1905_ = lean_apply_1(v_p_1888_, v___x_1904_);
v___x_1906_ = lean_unbox(v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec(v_a_1900_);
lean_dec_ref(v_expr_1897_);
lean_dec_ref(v_lctx_1896_);
lean_dec_ref(v_toElabInfo_1895_);
v___x_1907_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1907_);
v___x_1909_ = v___x_1902_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
if (lean_obj_tag(v_expr_1897_) == 1)
{
lean_object* v_fvarId_1911_; lean_object* v___x_1912_; 
v_fvarId_1911_ = lean_ctor_get(v_expr_1897_, 0);
lean_inc(v_fvarId_1911_);
lean_dec_ref_known(v_expr_1897_, 1);
v___x_1912_ = lean_local_ctx_find(v_lctx_1896_, v_fvarId_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_a_1900_);
lean_dec_ref(v_toElabInfo_1895_);
v___x_1913_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1913_);
v___x_1915_ = v___x_1902_;
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
lean_object* v_val_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1938_; 
v_val_1917_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1919_ = v___x_1912_;
v_isShared_1920_ = v_isSharedCheck_1938_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_val_1917_);
lean_dec(v___x_1912_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1938_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_stx_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1936_; 
v_stx_1921_ = lean_ctor_get(v_toElabInfo_1895_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_toElabInfo_1895_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_toElabInfo_1895_, 0);
lean_dec(v_unused_1937_);
v___x_1923_ = v_toElabInfo_1895_;
v_isShared_1924_ = v_isSharedCheck_1936_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_stx_1921_);
lean_dec(v_toElabInfo_1895_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1936_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_LocalDecl_userName(v_val_1917_);
lean_dec(v_val_1917_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 1, v_a_1900_);
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1900_);
v___x_1927_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_stx_1921_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1928_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1930_);
v___x_1932_ = v___x_1902_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec(v_a_1900_);
lean_dec_ref(v_expr_1897_);
lean_dec_ref(v_lctx_1896_);
lean_dec_ref(v_toElabInfo_1895_);
v___x_1939_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1939_);
v___x_1941_ = v___x_1902_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_expr_1897_);
lean_dec_ref(v_lctx_1896_);
lean_dec_ref(v_toElabInfo_1895_);
lean_dec_ref(v_p_1888_);
v_a_1944_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1899_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1899_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___lam__1___boxed(lean_object* v_p_1952_, lean_object* v_ctx_1953_, lean_object* v_ti_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Linter_List_binders___lam__1(v_p_1952_, v_ctx_1953_, v_ti_1954_);
return v_res_1956_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1958_, lean_object* v___x_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_){
_start:
{
if (lean_obj_tag(v_x_1960_) == 0)
{
lean_object* v_cs_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1976_; 
v_cs_1963_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1965_ = v_x_1960_;
v_isShared_1966_ = v_isSharedCheck_1976_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_cs_1963_);
lean_dec(v_x_1960_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1976_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_array_get_size(v_cs_1963_);
v___x_1969_ = lean_nat_dec_lt(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref(v_cs_1963_);
lean_dec(v___x_1959_);
lean_dec_ref(v_f_1958_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_x_1961_);
v___x_1971_ = v___x_1965_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_x_1961_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
else
{
size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1965_);
v___x_1973_ = ((size_t)0ULL);
v___x_1974_ = lean_usize_of_nat(v___x_1968_);
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_1958_, v___x_1959_, v_cs_1963_, v___x_1973_, v___x_1974_, v_x_1961_);
lean_dec_ref(v_cs_1963_);
return v___x_1975_;
}
}
}
else
{
lean_object* v_vs_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1990_; 
v_vs_1977_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1979_ = v_x_1960_;
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_vs_1977_);
lean_dec(v_x_1960_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_array_get_size(v_vs_1977_);
v___x_1983_ = lean_nat_dec_lt(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1985_; 
lean_dec_ref(v_vs_1977_);
lean_dec(v___x_1959_);
lean_dec_ref(v_f_1958_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 0);
lean_ctor_set(v___x_1979_, 0, v_x_1961_);
v___x_1985_ = v___x_1979_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_x_1961_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1979_);
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_of_nat(v___x_1982_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1958_, v___x_1959_, v_vs_1977_, v___x_1987_, v___x_1988_, v_x_1961_);
lean_dec_ref(v_vs_1977_);
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_f_1991_, lean_object* v___x_1992_, lean_object* v_as_1993_, size_t v_i_1994_, size_t v_stop_1995_, lean_object* v_b_1996_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_eq(v_i_1994_, v_stop_1995_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_array_uget_borrowed(v_as_1993_, v_i_1994_);
lean_inc(v___x_1999_);
lean_inc(v___x_1992_);
lean_inc_ref(v_f_1991_);
v___x_2000_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1991_, v___x_1992_, v___x_1999_, v_b_1996_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; size_t v___x_2002_; size_t v___x_2003_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1994_, v___x_2002_);
v_i_1994_ = v___x_2003_;
v_b_1996_ = v_a_2001_;
goto _start;
}
else
{
lean_dec(v___x_1992_);
lean_dec_ref(v_f_1991_);
return v___x_2000_;
}
}
else
{
lean_object* v___x_2005_; 
lean_dec(v___x_1992_);
lean_dec_ref(v_f_1991_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_b_1996_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_f_2006_, lean_object* v___x_2007_, lean_object* v_x_2008_, size_t v_x_2009_, size_t v_x_2010_, lean_object* v_x_2011_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v_cs_2013_; lean_object* v___x_2014_; size_t v___x_2015_; lean_object* v_j_2016_; lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v_cs_2013_ = lean_ctor_get(v_x_2008_, 0);
lean_inc_ref(v_cs_2013_);
lean_dec_ref_known(v_x_2008_, 1);
v___x_2014_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2015_ = lean_usize_shift_right(v_x_2009_, v_x_2010_);
v_j_2016_ = lean_usize_to_nat(v___x_2015_);
v___x_2017_ = lean_array_get_borrowed(v___x_2014_, v_cs_2013_, v_j_2016_);
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_shift_left(v___x_2018_, v_x_2010_);
v___x_2020_ = lean_usize_sub(v___x_2019_, v___x_2018_);
v___x_2021_ = lean_usize_land(v_x_2009_, v___x_2020_);
v___x_2022_ = ((size_t)5ULL);
v___x_2023_ = lean_usize_sub(v_x_2010_, v___x_2022_);
lean_inc(v___x_2017_);
lean_inc(v___x_2007_);
lean_inc_ref(v_f_2006_);
v___x_2024_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2006_, v___x_2007_, v___x_2017_, v___x_2021_, v___x_2023_, v_x_2011_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_j_2016_, v___x_2026_);
lean_dec(v_j_2016_);
v___x_2028_ = lean_array_get_size(v_cs_2013_);
v___x_2029_ = lean_nat_dec_lt(v___x_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_dec(v___x_2027_);
lean_dec_ref(v_cs_2013_);
lean_dec(v___x_2007_);
lean_dec_ref(v_f_2006_);
return v___x_2024_;
}
else
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2030_ = lean_usize_of_nat(v___x_2027_);
lean_dec(v___x_2027_);
v___x_2031_ = lean_usize_of_nat(v___x_2028_);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2006_, v___x_2007_, v_cs_2013_, v___x_2030_, v___x_2031_, v_a_2025_);
lean_dec_ref(v_cs_2013_);
return v___x_2032_;
}
}
else
{
lean_dec(v_j_2016_);
lean_dec_ref(v_cs_2013_);
lean_dec(v___x_2007_);
lean_dec_ref(v_f_2006_);
return v___x_2024_;
}
}
else
{
lean_object* v_vs_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2046_; 
v_vs_2033_ = lean_ctor_get(v_x_2008_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2035_ = v_x_2008_;
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_vs_2033_);
lean_dec(v_x_2008_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_usize_to_nat(v_x_2009_);
v___x_2038_ = lean_array_get_size(v_vs_2033_);
v___x_2039_ = lean_nat_dec_lt(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v___x_2037_);
lean_dec_ref(v_vs_2033_);
lean_dec(v___x_2007_);
lean_dec_ref(v_f_2006_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 0);
lean_ctor_set(v___x_2035_, 0, v_x_2011_);
v___x_2041_ = v___x_2035_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_x_2011_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
lean_del_object(v___x_2035_);
v___x_2043_ = lean_usize_of_nat(v___x_2037_);
lean_dec(v___x_2037_);
v___x_2044_ = lean_usize_of_nat(v___x_2038_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2006_, v___x_2007_, v_vs_2033_, v___x_2043_, v___x_2044_, v_x_2011_);
lean_dec_ref(v_vs_2033_);
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_2047_, lean_object* v___x_2048_, lean_object* v_t_2049_, lean_object* v_init_2050_, lean_object* v_start_2051_){
_start:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_nat_dec_eq(v_start_2051_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v_root_2055_; lean_object* v_tail_2056_; size_t v_shift_2057_; lean_object* v_tailOff_2058_; uint8_t v___x_2059_; 
v_root_2055_ = lean_ctor_get(v_t_2049_, 0);
lean_inc_ref(v_root_2055_);
v_tail_2056_ = lean_ctor_get(v_t_2049_, 1);
lean_inc_ref(v_tail_2056_);
v_shift_2057_ = lean_ctor_get_usize(v_t_2049_, 4);
v_tailOff_2058_ = lean_ctor_get(v_t_2049_, 3);
lean_inc(v_tailOff_2058_);
lean_dec_ref(v_t_2049_);
v___x_2059_ = lean_nat_dec_le(v_tailOff_2058_, v_start_2051_);
if (v___x_2059_ == 0)
{
size_t v___x_2060_; lean_object* v___x_2061_; 
lean_dec(v_tailOff_2058_);
v___x_2060_ = lean_usize_of_nat(v_start_2051_);
lean_inc(v___x_2048_);
lean_inc_ref(v_f_2047_);
v___x_2061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2047_, v___x_2048_, v_root_2055_, v___x_2060_, v_shift_2057_, v_init_2050_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v___x_2063_ = lean_array_get_size(v_tail_2056_);
v___x_2064_ = lean_nat_dec_lt(v___x_2053_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v_tail_2056_);
lean_dec(v___x_2048_);
lean_dec_ref(v_f_2047_);
return v___x_2061_;
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2063_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2047_, v___x_2048_, v_tail_2056_, v___x_2065_, v___x_2066_, v_a_2062_);
lean_dec_ref(v_tail_2056_);
return v___x_2067_;
}
}
else
{
lean_dec_ref(v_tail_2056_);
lean_dec(v___x_2048_);
lean_dec_ref(v_f_2047_);
return v___x_2061_;
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
lean_dec_ref(v_root_2055_);
v___x_2068_ = lean_nat_sub(v_start_2051_, v_tailOff_2058_);
lean_dec(v_tailOff_2058_);
v___x_2069_ = lean_array_get_size(v_tail_2056_);
v___x_2070_ = lean_nat_dec_lt(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v___x_2068_);
lean_dec_ref(v_tail_2056_);
lean_dec(v___x_2048_);
lean_dec_ref(v_f_2047_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_init_2050_);
return v___x_2071_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_usize_of_nat(v___x_2068_);
lean_dec(v___x_2068_);
v___x_2073_ = lean_usize_of_nat(v___x_2069_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2047_, v___x_2048_, v_tail_2056_, v___x_2072_, v___x_2073_, v_init_2050_);
lean_dec_ref(v_tail_2056_);
return v___x_2074_;
}
}
}
else
{
lean_object* v_root_2075_; lean_object* v_tail_2076_; lean_object* v___x_2077_; 
v_root_2075_ = lean_ctor_get(v_t_2049_, 0);
lean_inc_ref(v_root_2075_);
v_tail_2076_ = lean_ctor_get(v_t_2049_, 1);
lean_inc_ref(v_tail_2076_);
lean_dec_ref(v_t_2049_);
lean_inc(v___x_2048_);
lean_inc_ref(v_f_2047_);
v___x_2077_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2047_, v___x_2048_, v_root_2075_, v_init_2050_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v___x_2079_ = lean_array_get_size(v_tail_2076_);
v___x_2080_ = lean_nat_dec_lt(v___x_2053_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v_tail_2076_);
lean_dec(v___x_2048_);
lean_dec_ref(v_f_2047_);
return v___x_2077_;
}
else
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = lean_usize_of_nat(v___x_2079_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2047_, v___x_2048_, v_tail_2076_, v___x_2081_, v___x_2082_, v_a_2078_);
lean_dec_ref(v_tail_2076_);
return v___x_2083_;
}
}
else
{
lean_dec_ref(v_tail_2076_);
lean_dec(v___x_2048_);
lean_dec_ref(v_f_2047_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2084_, lean_object* v_ctx_x3f_2085_, lean_object* v_a_2086_, lean_object* v_x_2087_){
_start:
{
switch(lean_obj_tag(v_x_2087_))
{
case 0:
{
lean_object* v_i_2089_; lean_object* v_t_2090_; lean_object* v___x_2091_; 
v_i_2089_ = lean_ctor_get(v_x_2087_, 0);
lean_inc_ref(v_i_2089_);
v_t_2090_ = lean_ctor_get(v_x_2087_, 1);
lean_inc_ref(v_t_2090_);
lean_dec_ref_known(v_x_2087_, 2);
v___x_2091_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2089_, v_ctx_x3f_2085_);
v_ctx_x3f_2085_ = v___x_2091_;
v_x_2087_ = v_t_2090_;
goto _start;
}
case 1:
{
lean_object* v_i_2093_; lean_object* v_children_2094_; lean_object* v_a_2096_; 
v_i_2093_ = lean_ctor_get(v_x_2087_, 0);
lean_inc_ref(v_i_2093_);
v_children_2094_ = lean_ctor_get(v_x_2087_, 1);
lean_inc_ref(v_children_2094_);
lean_dec_ref_known(v_x_2087_, 2);
if (lean_obj_tag(v_ctx_x3f_2085_) == 0)
{
v_a_2096_ = v_a_2086_;
goto v___jp_2095_;
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2101_; 
v_val_2100_ = lean_ctor_get(v_ctx_x3f_2085_, 0);
lean_inc_ref(v_f_2084_);
lean_inc_ref(v_i_2093_);
lean_inc(v_val_2100_);
v___x_2101_ = lean_apply_4(v_f_2084_, v_val_2100_, v_i_2093_, v_a_2086_, lean_box(0));
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v_a_2096_ = v_a_2102_;
goto v___jp_2095_;
}
else
{
lean_dec_ref_known(v_ctx_x3f_2085_, 1);
lean_dec_ref(v_children_2094_);
lean_dec_ref(v_i_2093_);
lean_dec_ref(v_f_2084_);
return v___x_2101_;
}
}
v___jp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2085_, v_i_2093_);
lean_dec_ref(v_i_2093_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2084_, v___x_2097_, v_children_2094_, v_a_2096_, v___x_2098_);
return v___x_2099_;
}
}
default: 
{
lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_ctx_x3f_2085_);
lean_dec_ref(v_f_2084_);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_x_2087_, 0);
lean_dec(v_unused_2110_);
v___x_2104_ = v_x_2087_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_dec(v_x_2087_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 0);
lean_ctor_set(v___x_2104_, 0, v_a_2086_);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2086_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2111_, lean_object* v___x_2112_, lean_object* v_as_2113_, size_t v_i_2114_, size_t v_stop_2115_, lean_object* v_b_2116_){
_start:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_usize_dec_eq(v_i_2114_, v_stop_2115_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_array_uget_borrowed(v_as_2113_, v_i_2114_);
lean_inc(v___x_2119_);
lean_inc(v___x_2112_);
lean_inc_ref(v_f_2111_);
v___x_2120_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2111_, v___x_2112_, v_b_2116_, v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; size_t v___x_2122_; size_t v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2114_, v___x_2122_);
v_i_2114_ = v___x_2123_;
v_b_2116_ = v_a_2121_;
goto _start;
}
else
{
lean_dec(v___x_2112_);
lean_dec_ref(v_f_2111_);
return v___x_2120_;
}
}
else
{
lean_object* v___x_2125_; 
lean_dec(v___x_2112_);
lean_dec_ref(v_f_2111_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_b_2116_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_2126_, lean_object* v___x_2127_, lean_object* v_as_2128_, lean_object* v_i_2129_, lean_object* v_stop_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_i_boxed_2133_; size_t v_stop_boxed_2134_; lean_object* v_res_2135_; 
v_i_boxed_2133_ = lean_unbox_usize(v_i_2129_);
lean_dec(v_i_2129_);
v_stop_boxed_2134_ = lean_unbox_usize(v_stop_2130_);
lean_dec(v_stop_2130_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2126_, v___x_2127_, v_as_2128_, v_i_boxed_2133_, v_stop_boxed_2134_, v_b_2131_);
lean_dec_ref(v_as_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_2136_, lean_object* v___x_2137_, lean_object* v_as_2138_, lean_object* v_i_2139_, lean_object* v_stop_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_){
_start:
{
size_t v_i_boxed_2143_; size_t v_stop_boxed_2144_; lean_object* v_res_2145_; 
v_i_boxed_2143_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_stop_boxed_2144_ = lean_unbox_usize(v_stop_2140_);
lean_dec(v_stop_2140_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2136_, v___x_2137_, v_as_2138_, v_i_boxed_2143_, v_stop_boxed_2144_, v_b_2141_);
lean_dec_ref(v_as_2138_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_2146_, lean_object* v_ctx_x3f_2147_, lean_object* v_a_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2146_, v_ctx_x3f_2147_, v_a_2148_, v_x_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_2152_, lean_object* v___x_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2152_, v___x_2153_, v_x_2154_, v_x_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_f_2158_, lean_object* v___x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v___y_2164_){
_start:
{
size_t v_x_2501__boxed_2165_; size_t v_x_2502__boxed_2166_; lean_object* v_res_2167_; 
v_x_2501__boxed_2165_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_x_2502__boxed_2166_ = lean_unbox_usize(v_x_2162_);
lean_dec(v_x_2162_);
v_res_2167_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2158_, v___x_2159_, v_x_2160_, v_x_2501__boxed_2165_, v_x_2502__boxed_2166_, v_x_2163_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_2168_, lean_object* v___x_2169_, lean_object* v_t_2170_, lean_object* v_init_2171_, lean_object* v_start_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2168_, v___x_2169_, v_t_2170_, v_init_2171_, v_start_2172_);
lean_dec(v_start_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(lean_object* v_f_2175_, lean_object* v_init_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2175_, v___x_2179_, v_init_2176_, v_x_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(lean_object* v_f_2181_, lean_object* v_init_2182_, lean_object* v_x_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2181_, v_init_2182_, v_x_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(lean_object* v_f_2186_, lean_object* v_ctx_2187_, lean_object* v_info_2188_, lean_object* v_result_2189_){
_start:
{
if (lean_obj_tag(v_info_2188_) == 1)
{
lean_object* v_i_2191_; lean_object* v___x_2192_; 
v_i_2191_ = lean_ctor_get(v_info_2188_, 0);
lean_inc_ref(v_i_2191_);
lean_dec_ref_known(v_info_2188_, 1);
v___x_2192_ = lean_apply_3(v_f_2186_, v_ctx_2187_, v_i_2191_, lean_box(0));
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2205_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
if (lean_obj_tag(v_a_2193_) == 0)
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v_result_2189_);
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_result_2189_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v_val_2200_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_a_2193_, 1);
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_val_2200_);
lean_ctor_set(v___x_2201_, 1, v_result_2189_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2201_);
v___x_2203_ = v___x_2195_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_result_2189_);
v_a_2206_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2192_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2192_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v___x_2214_; 
lean_dec_ref(v_info_2188_);
lean_dec_ref(v_ctx_2187_);
lean_dec_ref(v_f_2186_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_result_2189_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(lean_object* v_f_2215_, lean_object* v_ctx_2216_, lean_object* v_info_2217_, lean_object* v_result_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_2215_, v_ctx_2216_, v_info_2217_, v_result_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(lean_object* v_t_2221_, lean_object* v_f_2222_){
_start:
{
lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2224_, 0, v_f_2222_);
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_2224_, v___x_2225_, v_t_2221_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(lean_object* v_t_2227_, lean_object* v_f_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2227_, v_f_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders(lean_object* v_t_2231_, lean_object* v_p_2232_){
_start:
{
lean_object* v___f_2234_; lean_object* v___x_2235_; 
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_Linter_List_binders___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2234_, 0, v_p_2232_);
v___x_2235_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2231_, v___f_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_binders___boxed(lean_object* v_t_2236_, lean_object* v_p_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Linter_List_binders(v_t_2236_, v_p_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(lean_object* v_00_u03b1_2240_, lean_object* v_t_2241_, lean_object* v_f_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(v_t_2241_, v_f_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_t_2246_, lean_object* v_f_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(v_00_u03b1_2245_, v_t_2246_, v_f_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(lean_object* v_00_u03b1_2250_, lean_object* v_f_2251_, lean_object* v_init_2252_, lean_object* v_x_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_2251_, v_init_2252_, v_x_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_f_2257_, lean_object* v_init_2258_, lean_object* v_x_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_2256_, v_f_2257_, v_init_2258_, v_x_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_2262_, lean_object* v_f_2263_, lean_object* v_ctx_x3f_2264_, lean_object* v_a_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_2263_, v_ctx_x3f_2264_, v_a_2265_, v_x_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_f_2270_, lean_object* v_ctx_x3f_2271_, lean_object* v_a_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_2269_, v_f_2270_, v_ctx_x3f_2271_, v_a_2272_, v_x_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2276_, lean_object* v_f_2277_, lean_object* v___x_2278_, lean_object* v_t_2279_, lean_object* v_init_2280_, lean_object* v_start_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2277_, v___x_2278_, v_t_2279_, v_init_2280_, v_start_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2284_, lean_object* v_f_2285_, lean_object* v___x_2286_, lean_object* v_t_2287_, lean_object* v_init_2288_, lean_object* v_start_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_2284_, v_f_2285_, v___x_2286_, v_t_2287_, v_init_2288_, v_start_2289_);
lean_dec(v_start_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2292_, lean_object* v_f_2293_, lean_object* v___x_2294_, lean_object* v_x_2295_, size_t v_x_2296_, size_t v_x_2297_, lean_object* v_x_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_2293_, v___x_2294_, v_x_2295_, v_x_2296_, v_x_2297_, v_x_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_f_2302_, lean_object* v___x_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_){
_start:
{
size_t v_x_2855__boxed_2309_; size_t v_x_2856__boxed_2310_; lean_object* v_res_2311_; 
v_x_2855__boxed_2309_ = lean_unbox_usize(v_x_2305_);
lean_dec(v_x_2305_);
v_x_2856__boxed_2310_ = lean_unbox_usize(v_x_2306_);
lean_dec(v_x_2306_);
v_res_2311_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_2301_, v_f_2302_, v___x_2303_, v_x_2304_, v_x_2855__boxed_2309_, v_x_2856__boxed_2310_, v_x_2307_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2312_, lean_object* v_f_2313_, lean_object* v___x_2314_, lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_2313_, v___x_2314_, v_as_2315_, v_i_2316_, v_stop_2317_, v_b_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2321_, lean_object* v_f_2322_, lean_object* v___x_2323_, lean_object* v_as_2324_, lean_object* v_i_2325_, lean_object* v_stop_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2326_);
lean_dec(v_stop_2326_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2321_, v_f_2322_, v___x_2323_, v_as_2324_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2327_);
lean_dec_ref(v_as_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_2332_, lean_object* v_f_2333_, lean_object* v___x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_2333_, v___x_2334_, v_x_2335_, v_x_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2339_, lean_object* v_f_2340_, lean_object* v___x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_2339_, v_f_2340_, v___x_2341_, v_x_2342_, v_x_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_2346_, lean_object* v_f_2347_, lean_object* v___x_2348_, lean_object* v_as_2349_, size_t v_i_2350_, size_t v_stop_2351_, lean_object* v_b_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_2347_, v___x_2348_, v_as_2349_, v_i_2350_, v_stop_2351_, v_b_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2355_, lean_object* v_f_2356_, lean_object* v___x_2357_, lean_object* v_as_2358_, lean_object* v_i_2359_, lean_object* v_stop_2360_, lean_object* v_b_2361_, lean_object* v___y_2362_){
_start:
{
size_t v_i_boxed_2363_; size_t v_stop_boxed_2364_; lean_object* v_res_2365_; 
v_i_boxed_2363_ = lean_unbox_usize(v_i_2359_);
lean_dec(v_i_2359_);
v_stop_boxed_2364_ = lean_unbox_usize(v_stop_2360_);
lean_dec(v_stop_2360_);
v_res_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_2355_, v_f_2356_, v___x_2357_, v_as_2358_, v_i_boxed_2363_, v_stop_boxed_2364_, v_b_2361_);
lean_dec_ref(v_as_2358_);
return v_res_2365_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(lean_object* v_as_x27_2372_, lean_object* v_b_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
if (lean_obj_tag(v_as_x27_2372_) == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_b_2373_);
return v___x_2377_;
}
else
{
lean_object* v_head_2378_; lean_object* v_snd_2379_; lean_object* v_tail_2380_; lean_object* v_fst_2381_; lean_object* v_fst_2382_; lean_object* v_snd_2383_; lean_object* v___x_2384_; 
v_head_2378_ = lean_ctor_get(v_as_x27_2372_, 0);
v_snd_2379_ = lean_ctor_get(v_head_2378_, 1);
v_tail_2380_ = lean_ctor_get(v_as_x27_2372_, 1);
v_fst_2381_ = lean_ctor_get(v_head_2378_, 0);
v_fst_2382_ = lean_ctor_get(v_snd_2379_, 0);
v_snd_2383_ = lean_ctor_get(v_snd_2379_, 1);
v___x_2384_ = lean_box(0);
if (lean_obj_tag(v_fst_2382_) == 1)
{
lean_object* v_str_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_str_2385_ = lean_ctor_get(v_fst_2382_, 1);
lean_inc_ref(v_str_2385_);
v___x_2386_ = l_Lean_Linter_List_stripBinderName(v_str_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Linter_List_allowedArrayNames));
v___x_2388_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2389_ = l_Lean_Linter_List_linter_listVariables;
v___x_2400_ = l_Lean_Expr_getAppNumArgs(v_snd_2383_);
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_sub(v___x_2400_, v___x_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = l_Lean_Expr_getRevArg_x21(v_snd_2383_, v___x_2402_);
v___x_2404_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2405_ = l_Lean_Expr_isAppOf(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2407_ = l_Lean_Expr_isAppOf(v___x_2403_, v___x_2406_);
lean_dec_ref(v___x_2403_);
if (v___x_2407_ == 0)
{
goto v___jp_2390_;
}
else
{
goto v___jp_2396_;
}
}
else
{
lean_dec_ref(v___x_2403_);
goto v___jp_2396_;
}
v___jp_2390_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
v___x_2392_ = l_Lean_stringToMessageData(v___x_2386_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc(v_fst_2381_);
v___x_2394_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2389_, v_fst_2381_, v___x_2393_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_dec_ref_known(v___x_2394_, 1);
v_as_x27_2372_ = v_tail_2380_;
v_b_2373_ = v___x_2384_;
goto _start;
}
else
{
return v___x_2394_;
}
}
v___jp_2396_:
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2398_ = lean_string_dec_eq(v___x_2386_, v___x_2397_);
if (v___x_2398_ == 0)
{
goto v___jp_2390_;
}
else
{
lean_dec_ref(v___x_2386_);
v_as_x27_2372_ = v_tail_2380_;
v_b_2373_ = v___x_2384_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_2386_);
v_as_x27_2372_ = v_tail_2380_;
v_b_2373_ = v___x_2384_;
goto _start;
}
}
else
{
v_as_x27_2372_ = v_tail_2380_;
v_b_2373_ = v___x_2384_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(lean_object* v_as_x27_2410_, lean_object* v_b_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_2410_, v_b_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v_as_x27_2410_);
return v_res_2415_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(lean_object* v_as_x27_2422_, lean_object* v_b_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
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
v___x_2437_ = ((lean_object*)(l_Lean_Linter_List_allowedListNames));
v___x_2438_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2439_ = l_Lean_Linter_List_linter_listVariables;
v___x_2453_ = l_Lean_Expr_getAppNumArgs(v_snd_2433_);
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_sub(v___x_2453_, v___x_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = l_Lean_Expr_getRevArg_x21(v_snd_2433_, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2458_ = l_Lean_Expr_isAppOf(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2460_ = l_Lean_Expr_isAppOf(v___x_2456_, v___x_2459_);
lean_dec_ref(v___x_2456_);
if (v___x_2460_ == 0)
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
lean_dec_ref(v___x_2456_);
goto v___jp_2446_;
}
v___jp_2440_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
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
v___x_2447_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2));
v___x_2448_ = lean_string_dec_eq(v___x_2436_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2450_ = lean_string_dec_eq(v___x_2436_, v___x_2449_);
if (v___x_2450_ == 0)
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(lean_object* v_as_x27_2463_, lean_object* v_b_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_2463_, v_b_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v_as_x27_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
if (lean_obj_tag(v_a_2469_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = l_List_reverse___redArg(v_a_2470_);
return v___x_2471_;
}
else
{
lean_object* v_head_2472_; lean_object* v_snd_2473_; lean_object* v_tail_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2486_; 
v_head_2472_ = lean_ctor_get(v_a_2469_, 0);
lean_inc(v_head_2472_);
v_snd_2473_ = lean_ctor_get(v_head_2472_, 1);
v_tail_2474_ = lean_ctor_get(v_a_2469_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v_a_2469_, 0);
lean_dec(v_unused_2487_);
v___x_2476_ = v_a_2469_;
v_isShared_2477_ = v_isSharedCheck_2486_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_tail_2474_);
lean_dec(v_a_2469_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2486_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_snd_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_snd_2478_ = lean_ctor_get(v_snd_2473_, 1);
v___x_2479_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3));
v___x_2480_ = l_Lean_Expr_isAppOf(v_snd_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_del_object(v___x_2476_);
lean_dec(v_head_2472_);
v_a_2469_ = v_tail_2474_;
goto _start;
}
else
{
lean_object* v___x_2483_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v_a_2470_);
v___x_2483_ = v___x_2476_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_head_2472_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_a_2470_);
v___x_2483_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
v_a_2469_ = v_tail_2474_;
v_a_2470_ = v___x_2483_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(uint8_t v_v_2488_, lean_object* v_x_2489_){
_start:
{
return v_v_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(lean_object* v_v_2490_, lean_object* v_x_2491_){
_start:
{
uint8_t v_v_12942__boxed_2492_; uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_v_12942__boxed_2492_ = lean_unbox(v_v_2490_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v_v_12942__boxed_2492_, v_x_2491_);
lean_dec_ref(v_x_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
if (lean_obj_tag(v_a_2495_) == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = l_List_reverse___redArg(v_a_2496_);
return v___x_2497_;
}
else
{
lean_object* v_head_2498_; lean_object* v_snd_2499_; lean_object* v_tail_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2512_; 
v_head_2498_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_head_2498_);
v_snd_2499_ = lean_ctor_get(v_head_2498_, 1);
v_tail_2500_ = lean_ctor_get(v_a_2495_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2495_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v_a_2495_, 0);
lean_dec(v_unused_2513_);
v___x_2502_ = v_a_2495_;
v_isShared_2503_ = v_isSharedCheck_2512_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_tail_2500_);
lean_dec(v_a_2495_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2512_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_snd_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_snd_2504_ = lean_ctor_get(v_snd_2499_, 1);
v___x_2505_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3));
v___x_2506_ = l_Lean_Expr_isAppOf(v_snd_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_del_object(v___x_2502_);
lean_dec(v_head_2498_);
v_a_2495_ = v_tail_2500_;
goto _start;
}
else
{
lean_object* v___x_2509_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v_a_2496_);
v___x_2509_ = v___x_2502_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_head_2498_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_a_2496_);
v___x_2509_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
v_a_2495_ = v_tail_2500_;
v_a_2496_ = v___x_2509_;
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
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(lean_object* v_as_x27_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
if (lean_obj_tag(v_as_x27_2517_) == 0)
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2518_);
return v___x_2522_;
}
else
{
lean_object* v_head_2523_; lean_object* v_snd_2524_; lean_object* v_tail_2525_; lean_object* v_fst_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___x_2529_; 
v_head_2523_ = lean_ctor_get(v_as_x27_2517_, 0);
v_snd_2524_ = lean_ctor_get(v_head_2523_, 1);
v_tail_2525_ = lean_ctor_get(v_as_x27_2517_, 1);
v_fst_2526_ = lean_ctor_get(v_head_2523_, 0);
v_fst_2527_ = lean_ctor_get(v_snd_2524_, 0);
v_snd_2528_ = lean_ctor_get(v_snd_2524_, 1);
v___x_2529_ = lean_box(0);
if (lean_obj_tag(v_fst_2527_) == 1)
{
lean_object* v_str_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_str_2530_ = lean_ctor_get(v_fst_2527_, 1);
lean_inc_ref(v_str_2530_);
v___x_2531_ = l_Lean_Linter_List_stripBinderName(v_str_2530_);
v___x_2532_ = ((lean_object*)(l_Lean_Linter_List_allowedVectorNames));
v___x_2533_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2534_ = l_Lean_Linter_List_linter_listVariables;
v___x_2541_ = l_Lean_Expr_getAppNumArgs(v_snd_2528_);
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = lean_nat_sub(v___x_2541_, v___x_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = l_Lean_Expr_getRevArg_x21(v_snd_2528_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2546_ = l_Lean_Expr_isAppOf(v___x_2544_, v___x_2545_);
lean_dec_ref(v___x_2544_);
if (v___x_2546_ == 0)
{
goto v___jp_2535_;
}
else
{
lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2));
v___x_2548_ = lean_string_dec_eq(v___x_2531_, v___x_2547_);
if (v___x_2548_ == 0)
{
goto v___jp_2535_;
}
else
{
lean_dec_ref(v___x_2531_);
v_as_x27_2517_ = v_tail_2525_;
v_b_2518_ = v___x_2529_;
goto _start;
}
}
v___jp_2535_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
v___x_2537_ = l_Lean_stringToMessageData(v___x_2531_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
lean_inc(v_fst_2526_);
v___x_2539_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(v___x_2534_, v_fst_2526_, v___x_2538_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref_known(v___x_2539_, 1);
v_as_x27_2517_ = v_tail_2525_;
v_b_2518_ = v___x_2529_;
goto _start;
}
else
{
return v___x_2539_;
}
}
}
else
{
lean_dec_ref(v___x_2531_);
v_as_x27_2517_ = v_tail_2525_;
v_b_2518_ = v___x_2529_;
goto _start;
}
}
else
{
v_as_x27_2517_ = v_tail_2525_;
v_b_2518_ = v___x_2529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(lean_object* v_as_x27_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_2552_, v_b_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v_as_x27_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
if (lean_obj_tag(v_a_2558_) == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = l_List_reverse___redArg(v_a_2559_);
return v___x_2560_;
}
else
{
lean_object* v_head_2561_; lean_object* v_snd_2562_; lean_object* v_tail_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2575_; 
v_head_2561_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_head_2561_);
v_snd_2562_ = lean_ctor_get(v_head_2561_, 1);
v_tail_2563_ = lean_ctor_get(v_a_2558_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_a_2558_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_a_2558_, 0);
lean_dec(v_unused_2576_);
v___x_2565_ = v_a_2558_;
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_tail_2563_);
lean_dec(v_a_2558_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_snd_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_snd_2567_ = lean_ctor_get(v_snd_2562_, 1);
v___x_2568_ = ((lean_object*)(l_Lean_Linter_List_numericalWidths___lam__1___closed__4));
v___x_2569_ = l_Lean_Expr_isAppOf(v_snd_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_del_object(v___x_2565_);
lean_dec(v_head_2561_);
v_a_2558_ = v_tail_2563_;
goto _start;
}
else
{
lean_object* v___x_2572_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v_a_2559_);
v___x_2572_ = v___x_2565_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_head_2561_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_a_2559_);
v___x_2572_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
v_a_2558_ = v_tail_2563_;
v_a_2559_ = v___x_2572_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(uint8_t v_v_2577_, lean_object* v_as_2578_, size_t v_sz_2579_, size_t v_i_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_lt(v_i_2580_, v_sz_2579_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_b_2581_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v_a_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v_b_2581_);
v___x_2587_ = lean_box(v_v_2577_);
v___f_2588_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2588_, 0, v___x_2587_);
v___x_2589_ = lean_box(0);
v_a_2590_ = lean_array_uget_borrowed(v_as_2578_, v_i_2580_);
lean_inc(v_a_2590_);
v___x_2591_ = l_Lean_Linter_List_binders(v_a_2590_, v___f_2588_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_n(v_a_2592_, 2);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = lean_box(0);
v___x_2594_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2592_, v___x_2593_);
v___x_2595_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2594_, v___x_2589_, v___y_2582_, v___y_2583_);
lean_dec(v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2595_, 1);
lean_inc(v_a_2592_);
v___x_2596_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2592_, v___x_2593_);
v___x_2597_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2596_, v___x_2589_, v___y_2582_, v___y_2583_);
lean_dec(v___x_2596_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2597_, 1);
v___x_2598_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2592_, v___x_2593_);
v___x_2599_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2598_, v___x_2589_, v___y_2582_, v___y_2583_);
lean_dec(v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; 
lean_dec_ref_known(v___x_2599_, 1);
v___x_2600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2580_, v___x_2601_);
v_i_2580_ = v___x_2602_;
v_b_2581_ = v___x_2600_;
goto _start;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
v_a_2604_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2599_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2599_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_a_2592_);
v_a_2612_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2597_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2597_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_a_2592_);
v_a_2620_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2595_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2595_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2640_; 
v_a_2628_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2630_ = v___x_2591_;
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2591_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_ref_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v_ref_2632_ = lean_ctor_get(v___y_2582_, 7);
v___x_2633_ = lean_io_error_to_string(v_a_2628_);
v___x_2634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = l_Lean_MessageData_ofFormat(v___x_2634_);
lean_inc(v_ref_2632_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_ref_2632_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2636_);
v___x_2638_ = v___x_2630_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(lean_object* v_v_2641_, lean_object* v_as_2642_, lean_object* v_sz_2643_, lean_object* v_i_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
uint8_t v_v_13122__boxed_2649_; size_t v_sz_boxed_2650_; size_t v_i_boxed_2651_; lean_object* v_res_2652_; 
v_v_13122__boxed_2649_ = lean_unbox(v_v_2641_);
v_sz_boxed_2650_ = lean_unbox_usize(v_sz_2643_);
lean_dec(v_sz_2643_);
v_i_boxed_2651_ = lean_unbox_usize(v_i_2644_);
lean_dec(v_i_2644_);
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v_v_13122__boxed_2649_, v_as_2642_, v_sz_boxed_2650_, v_i_boxed_2651_, v_b_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_as_2642_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(uint8_t v_v_2653_, lean_object* v_as_2654_, size_t v_sz_2655_, size_t v_i_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = lean_usize_dec_lt(v_i_2656_, v_sz_2655_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_b_2657_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; lean_object* v_a_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v_b_2657_);
v___x_2663_ = lean_box(v_v_2653_);
v___f_2664_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2664_, 0, v___x_2663_);
v___x_2665_ = lean_box(0);
v_a_2666_ = lean_array_uget_borrowed(v_as_2654_, v_i_2656_);
lean_inc(v_a_2666_);
v___x_2667_ = l_Lean_Linter_List_binders(v_a_2666_, v___f_2664_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_n(v_a_2668_, 2);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = lean_box(0);
v___x_2670_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2668_, v___x_2669_);
v___x_2671_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2670_, v___x_2665_, v___y_2658_, v___y_2659_);
lean_dec(v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2671_, 1);
lean_inc(v_a_2668_);
v___x_2672_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2668_, v___x_2669_);
v___x_2673_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2672_, v___x_2665_, v___y_2658_, v___y_2659_);
lean_dec(v___x_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref_known(v___x_2673_, 1);
v___x_2674_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2668_, v___x_2669_);
v___x_2675_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2674_, v___x_2665_, v___y_2658_, v___y_2659_);
lean_dec(v___x_2674_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2676_; size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
lean_dec_ref_known(v___x_2675_, 1);
v___x_2676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0));
v___x_2677_ = ((size_t)1ULL);
v___x_2678_ = lean_usize_add(v_i_2656_, v___x_2677_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v_v_2653_, v_as_2654_, v_sz_2655_, v___x_2678_, v___x_2676_, v___y_2658_, v___y_2659_);
return v___x_2679_;
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2675_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2675_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2668_);
v_a_2688_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2673_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2673_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2668_);
v_a_2696_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2671_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2671_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2716_; 
v_a_2704_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2706_ = v___x_2667_;
v_isShared_2707_ = v_isSharedCheck_2716_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2667_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2716_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_ref_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v_ref_2708_ = lean_ctor_get(v___y_2658_, 7);
v___x_2709_ = lean_io_error_to_string(v_a_2704_);
v___x_2710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = l_Lean_MessageData_ofFormat(v___x_2710_);
lean_inc(v_ref_2708_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_ref_2708_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2712_);
v___x_2714_ = v___x_2706_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(lean_object* v_v_2717_, lean_object* v_as_2718_, lean_object* v_sz_2719_, lean_object* v_i_2720_, lean_object* v_b_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v_v_13249__boxed_2725_; size_t v_sz_boxed_2726_; size_t v_i_boxed_2727_; lean_object* v_res_2728_; 
v_v_13249__boxed_2725_ = lean_unbox(v_v_2717_);
v_sz_boxed_2726_ = lean_unbox_usize(v_sz_2719_);
lean_dec(v_sz_2719_);
v_i_boxed_2727_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v_v_13249__boxed_2725_, v_as_2718_, v_sz_boxed_2726_, v_i_boxed_2727_, v_b_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_as_2718_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(lean_object* v_init_2729_, uint8_t v_v_2730_, lean_object* v_n_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
if (lean_obj_tag(v_n_2731_) == 0)
{
lean_object* v_cs_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; size_t v_sz_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v_cs_2736_ = lean_ctor_get(v_n_2731_, 0);
v___x_2737_ = lean_box(0);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_b_2732_);
v_sz_2739_ = lean_array_size(v_cs_2736_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2729_, v_v_2730_, v_cs_2736_, v_sz_2739_, v___x_2740_, v___x_2738_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2756_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_fst_2746_; 
v_fst_2746_ = lean_ctor_get(v_a_2742_, 0);
if (lean_obj_tag(v_fst_2746_) == 0)
{
lean_object* v_snd_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v_snd_2747_ = lean_ctor_get(v_a_2742_, 1);
lean_inc(v_snd_2747_);
lean_dec(v_a_2742_);
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_snd_2747_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2748_);
v___x_2750_ = v___x_2744_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
else
{
lean_object* v_val_2752_; lean_object* v___x_2754_; 
lean_inc_ref(v_fst_2746_);
lean_dec(v_a_2742_);
v_val_2752_ = lean_ctor_get(v_fst_2746_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v_fst_2746_, 1);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_val_2752_);
v___x_2754_ = v___x_2744_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_val_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2741_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2741_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_vs_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; size_t v_sz_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v_vs_2765_ = lean_ctor_get(v_n_2731_, 0);
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_b_2732_);
v_sz_2768_ = lean_array_size(v_vs_2765_);
v___x_2769_ = ((size_t)0ULL);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v_v_2730_, v_vs_2765_, v_sz_2768_, v___x_2769_, v___x_2767_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2785_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2785_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2785_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_fst_2775_; 
v_fst_2775_ = lean_ctor_get(v_a_2771_, 0);
if (lean_obj_tag(v_fst_2775_) == 0)
{
lean_object* v_snd_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v_snd_2776_ = lean_ctor_get(v_a_2771_, 1);
lean_inc(v_snd_2776_);
lean_dec(v_a_2771_);
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_snd_2776_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v___x_2777_);
v___x_2779_ = v___x_2773_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
lean_object* v_val_2781_; lean_object* v___x_2783_; 
lean_inc_ref(v_fst_2775_);
lean_dec(v_a_2771_);
v_val_2781_ = lean_ctor_get(v_fst_2775_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v_fst_2775_, 1);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_val_2781_);
v___x_2783_ = v___x_2773_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_val_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2770_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2770_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(lean_object* v_init_2794_, uint8_t v_v_2795_, lean_object* v_as_2796_, size_t v_sz_2797_, size_t v_i_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_usize_dec_lt(v_i_2798_, v_sz_2797_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_b_2799_);
return v___x_2804_;
}
else
{
lean_object* v_snd_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2839_; 
v_snd_2805_ = lean_ctor_get(v_b_2799_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_b_2799_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v_b_2799_, 0);
lean_dec(v_unused_2840_);
v___x_2807_ = v_b_2799_;
v_isShared_2808_ = v_isSharedCheck_2839_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_snd_2805_);
lean_dec(v_b_2799_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2839_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2811_; 
v___x_2809_ = lean_box(0);
v_a_2810_ = lean_array_uget_borrowed(v_as_2796_, v_i_2798_);
lean_inc(v_snd_2805_);
v___x_2811_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2794_, v_v_2795_, v_a_2810_, v_snd_2805_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2830_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2830_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2830_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_a_2812_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2816_);
v___x_2818_ = v___x_2807_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_snd_2805_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2818_);
v___x_2820_ = v___x_2814_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; 
lean_del_object(v___x_2814_);
lean_dec(v_snd_2805_);
v_a_2823_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v_a_2812_, 1);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v_a_2823_);
lean_ctor_set(v___x_2807_, 0, v___x_2809_);
v___x_2825_ = v___x_2807_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_a_2823_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
size_t v___x_2826_; size_t v___x_2827_; 
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2798_, v___x_2826_);
v_i_2798_ = v___x_2827_;
v_b_2799_ = v___x_2825_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2807_);
lean_dec(v_snd_2805_);
v_a_2831_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2811_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2811_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(lean_object* v_init_2841_, lean_object* v_v_2842_, lean_object* v_as_2843_, lean_object* v_sz_2844_, lean_object* v_i_2845_, lean_object* v_b_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v_v_13373__boxed_2850_; size_t v_sz_boxed_2851_; size_t v_i_boxed_2852_; lean_object* v_res_2853_; 
v_v_13373__boxed_2850_ = lean_unbox(v_v_2842_);
v_sz_boxed_2851_ = lean_unbox_usize(v_sz_2844_);
lean_dec(v_sz_2844_);
v_i_boxed_2852_ = lean_unbox_usize(v_i_2845_);
lean_dec(v_i_2845_);
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_2841_, v_v_13373__boxed_2850_, v_as_2843_, v_sz_boxed_2851_, v_i_boxed_2852_, v_b_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_as_2843_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(lean_object* v_init_2854_, lean_object* v_v_2855_, lean_object* v_n_2856_, lean_object* v_b_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v_v_13393__boxed_2861_; lean_object* v_res_2862_; 
v_v_13393__boxed_2861_ = lean_unbox(v_v_2855_);
v_res_2862_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_2854_, v_v_13393__boxed_2861_, v_n_2856_, v_b_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_n_2856_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(uint8_t v_v_2863_, lean_object* v_as_2864_, size_t v_sz_2865_, size_t v_i_2866_, lean_object* v_b_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_usize_dec_lt(v_i_2866_, v_sz_2865_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_b_2867_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_b_2867_);
v___x_2873_ = lean_box(v_v_2863_);
v___f_2874_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2874_, 0, v___x_2873_);
v___x_2875_ = lean_box(0);
v_a_2876_ = lean_array_uget_borrowed(v_as_2864_, v_i_2866_);
lean_inc(v_a_2876_);
v___x_2877_ = l_Lean_Linter_List_binders(v_a_2876_, v___f_2874_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc_n(v_a_2878_, 2);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = lean_box(0);
v___x_2880_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2878_, v___x_2879_);
v___x_2881_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2880_, v___x_2875_, v___y_2868_, v___y_2869_);
lean_dec(v___x_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref_known(v___x_2881_, 1);
lean_inc(v_a_2878_);
v___x_2882_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2878_, v___x_2879_);
v___x_2883_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2882_, v___x_2875_, v___y_2868_, v___y_2869_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec_ref_known(v___x_2883_, 1);
v___x_2884_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2878_, v___x_2879_);
v___x_2885_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2884_, v___x_2875_, v___y_2868_, v___y_2869_);
lean_dec(v___x_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; 
lean_dec_ref_known(v___x_2885_, 1);
v___x_2886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2866_, v___x_2887_);
v_i_2866_ = v___x_2888_;
v_b_2867_ = v___x_2886_;
goto _start;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
v_a_2890_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2885_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2885_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_a_2878_);
v_a_2898_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2883_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2883_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2878_);
v_a_2906_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2881_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2881_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2926_; 
v_a_2914_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2916_ = v___x_2877_;
v_isShared_2917_ = v_isSharedCheck_2926_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2877_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2926_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_ref_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_ref_2918_ = lean_ctor_get(v___y_2868_, 7);
v___x_2919_ = lean_io_error_to_string(v_a_2914_);
v___x_2920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
v___x_2921_ = l_Lean_MessageData_ofFormat(v___x_2920_);
lean_inc(v_ref_2918_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v_ref_2918_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2922_);
v___x_2924_ = v___x_2916_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(lean_object* v_v_2927_, lean_object* v_as_2928_, lean_object* v_sz_2929_, lean_object* v_i_2930_, lean_object* v_b_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_v_13577__boxed_2935_; size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_v_13577__boxed_2935_ = lean_unbox(v_v_2927_);
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2929_);
lean_dec(v_sz_2929_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2930_);
lean_dec(v_i_2930_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v_v_13577__boxed_2935_, v_as_2928_, v_sz_boxed_2936_, v_i_boxed_2937_, v_b_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v_as_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(uint8_t v_v_2939_, lean_object* v_as_2940_, size_t v_sz_2941_, size_t v_i_2942_, lean_object* v_b_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v___x_2947_; 
v___x_2947_ = lean_usize_dec_lt(v_i_2942_, v_sz_2941_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_b_2943_);
return v___x_2948_;
}
else
{
lean_object* v___x_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v___x_2953_; 
lean_dec_ref(v_b_2943_);
v___x_2949_ = lean_box(v_v_2939_);
v___f_2950_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2950_, 0, v___x_2949_);
v___x_2951_ = lean_box(0);
v_a_2952_ = lean_array_uget_borrowed(v_as_2940_, v_i_2942_);
lean_inc(v_a_2952_);
v___x_2953_ = l_Lean_Linter_List_binders(v_a_2952_, v___f_2950_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc_n(v_a_2954_, 2);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = lean_box(0);
v___x_2956_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_2954_, v___x_2955_);
v___x_2957_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_2956_, v___x_2951_, v___y_2944_, v___y_2945_);
lean_dec(v___x_2956_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref_known(v___x_2957_, 1);
lean_inc(v_a_2954_);
v___x_2958_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_2954_, v___x_2955_);
v___x_2959_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_2958_, v___x_2951_, v___y_2944_, v___y_2945_);
lean_dec(v___x_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_dec_ref_known(v___x_2959_, 1);
v___x_2960_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_2954_, v___x_2955_);
v___x_2961_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_2960_, v___x_2951_, v___y_2944_, v___y_2945_);
lean_dec(v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2961_, 1);
v___x_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0));
v___x_2963_ = ((size_t)1ULL);
v___x_2964_ = lean_usize_add(v_i_2942_, v___x_2963_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v_v_2939_, v_as_2940_, v_sz_2941_, v___x_2964_, v___x_2962_, v___y_2944_, v___y_2945_);
return v___x_2965_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v_a_2966_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2961_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2961_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_a_2954_);
v_a_2974_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2959_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2959_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_a_2954_);
v_a_2982_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2957_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2957_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3002_; 
v_a_2990_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2992_ = v___x_2953_;
v_isShared_2993_ = v_isSharedCheck_3002_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2953_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3002_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_ref_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v_ref_2994_ = lean_ctor_get(v___y_2944_, 7);
v___x_2995_ = lean_io_error_to_string(v_a_2990_);
v___x_2996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
v___x_2997_ = l_Lean_MessageData_ofFormat(v___x_2996_);
lean_inc(v_ref_2994_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_ref_2994_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2998_);
v___x_3000_ = v___x_2992_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(lean_object* v_v_3003_, lean_object* v_as_3004_, lean_object* v_sz_3005_, lean_object* v_i_3006_, lean_object* v_b_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
uint8_t v_v_13704__boxed_3011_; size_t v_sz_boxed_3012_; size_t v_i_boxed_3013_; lean_object* v_res_3014_; 
v_v_13704__boxed_3011_ = lean_unbox(v_v_3003_);
v_sz_boxed_3012_ = lean_unbox_usize(v_sz_3005_);
lean_dec(v_sz_3005_);
v_i_boxed_3013_ = lean_unbox_usize(v_i_3006_);
lean_dec(v_i_3006_);
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v_v_13704__boxed_3011_, v_as_3004_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec_ref(v_as_3004_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(uint8_t v_v_3015_, lean_object* v_t_3016_, lean_object* v_init_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_root_3021_; lean_object* v_tail_3022_; lean_object* v___x_3023_; 
v_root_3021_ = lean_ctor_get(v_t_3016_, 0);
v_tail_3022_ = lean_ctor_get(v_t_3016_, 1);
v___x_3023_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_3017_, v_v_3015_, v_root_3021_, v_init_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3060_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3060_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3060_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; 
v_a_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v_a_3024_, 1);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_a_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; size_t v_sz_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
lean_del_object(v___x_3026_);
v_a_3032_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v_a_3024_, 1);
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v_a_3032_);
v_sz_3035_ = lean_array_size(v_tail_3022_);
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v_v_3015_, v_tail_3022_, v_sz_3035_, v___x_3036_, v___x_3034_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3051_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; 
v_fst_3042_ = lean_ctor_get(v_a_3038_, 0);
if (lean_obj_tag(v_fst_3042_) == 0)
{
lean_object* v_snd_3043_; lean_object* v___x_3045_; 
v_snd_3043_ = lean_ctor_get(v_a_3038_, 1);
lean_inc(v_snd_3043_);
lean_dec(v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_snd_3043_);
v___x_3045_ = v___x_3040_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_snd_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
else
{
lean_object* v_val_3047_; lean_object* v___x_3049_; 
lean_inc_ref(v_fst_3042_);
lean_dec(v_a_3038_);
v_val_3047_ = lean_ctor_get(v_fst_3042_, 0);
lean_inc(v_val_3047_);
lean_dec_ref_known(v_fst_3042_, 1);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_val_3047_);
v___x_3049_ = v___x_3040_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_val_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3037_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3037_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3023_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3023_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(lean_object* v_v_3069_, lean_object* v_t_3070_, lean_object* v_init_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
uint8_t v_v_13828__boxed_3075_; lean_object* v_res_3076_; 
v_v_13828__boxed_3075_ = lean_unbox(v_v_3069_);
v_res_3076_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_v_13828__boxed_3075_, v_t_3070_, v_init_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_t_3070_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0(lean_object* v_stx_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_scopes_3086_; lean_object* v___x_3087_; lean_object* v_opts_3088_; lean_object* v___x_3089_; lean_object* v_name_3090_; lean_object* v_map_3091_; lean_object* v___x_3092_; 
v___x_3081_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3082_ = lean_st_ref_get(v___y_3079_);
v_scopes_3086_ = lean_ctor_get(v___x_3082_, 2);
lean_inc(v_scopes_3086_);
lean_dec(v___x_3082_);
v___x_3087_ = l_List_head_x21___redArg(v___x_3081_, v_scopes_3086_);
lean_dec(v_scopes_3086_);
v_opts_3088_ = lean_ctor_get(v___x_3087_, 1);
lean_inc_ref(v_opts_3088_);
lean_dec(v___x_3087_);
v___x_3089_ = l_Lean_Linter_List_linter_listVariables;
v_name_3090_ = lean_ctor_get(v___x_3089_, 0);
v_map_3091_ = lean_ctor_get(v_opts_3088_, 0);
lean_inc(v_map_3091_);
lean_dec_ref(v_opts_3088_);
v___x_3092_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3091_, v_name_3090_);
lean_dec(v_map_3091_);
if (lean_obj_tag(v___x_3092_) == 0)
{
goto v___jp_3083_;
}
else
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3125_; 
v_val_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3125_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3125_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
if (lean_obj_tag(v_val_3093_) == 1)
{
uint8_t v_v_3097_; 
v_v_3097_ = lean_ctor_get_uint8(v_val_3093_, 0);
lean_dec_ref_known(v_val_3093_, 0);
if (v_v_3097_ == 0)
{
lean_del_object(v___x_3095_);
goto v___jp_3083_;
}
else
{
lean_object* v___x_3098_; lean_object* v_messages_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_st_ref_get(v___y_3079_);
v_messages_3099_ = lean_ctor_get(v___x_3098_, 1);
lean_inc_ref(v_messages_3099_);
lean_dec(v___x_3098_);
v___x_3100_ = l_Lean_MessageLog_hasErrors(v_messages_3099_);
lean_dec_ref(v_messages_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v_infoState_3107_; uint8_t v_enabled_3108_; 
v___x_3101_ = lean_st_ref_get(v___y_3079_);
v_infoState_3107_ = lean_ctor_get(v___x_3101_, 8);
lean_inc_ref(v_infoState_3107_);
lean_dec(v___x_3101_);
v_enabled_3108_ = lean_ctor_get_uint8(v_infoState_3107_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3107_);
if (v_enabled_3108_ == 0)
{
goto v___jp_3102_;
}
else
{
if (v___x_3100_ == 0)
{
lean_object* v___x_3109_; lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_del_object(v___x_3095_);
v___x_3109_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_3079_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v___x_3111_ = lean_box(0);
v___x_3112_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_v_3097_, v_a_3110_, v___x_3111_, v___y_3078_, v___y_3079_);
lean_dec(v_a_3110_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3112_, 0);
lean_dec(v_unused_3120_);
v___x_3114_ = v___x_3112_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v___x_3112_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3111_);
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3111_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
return v___x_3112_;
}
}
else
{
goto v___jp_3102_;
}
}
v___jp_3102_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = lean_box(0);
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3103_);
v___x_3105_ = v___x_3095_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_box(0);
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3121_);
v___x_3123_ = v___x_3095_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_del_object(v___x_3095_);
lean_dec(v_val_3093_);
goto v___jp_3083_;
}
}
}
v___jp_3083_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(lean_object* v_stx_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v_stx_3126_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(lean_object* v_as_3144_, lean_object* v_as_x27_3145_, lean_object* v_b_3146_, lean_object* v_a_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v_as_x27_3145_, v_b_3146_, v___y_3148_, v___y_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(lean_object* v_as_3152_, lean_object* v_as_x27_3153_, lean_object* v_b_3154_, lean_object* v_a_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(v_as_3152_, v_as_x27_3153_, v_b_3154_, v_a_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v_as_x27_3153_);
lean_dec(v_as_3152_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(lean_object* v_as_3160_, lean_object* v_as_x27_3161_, lean_object* v_b_3162_, lean_object* v_a_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v_as_x27_3161_, v_b_3162_, v___y_3164_, v___y_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(lean_object* v_as_3168_, lean_object* v_as_x27_3169_, lean_object* v_b_3170_, lean_object* v_a_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(v_as_3168_, v_as_x27_3169_, v_b_3170_, v_a_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v_as_x27_3169_);
lean_dec(v_as_3168_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(lean_object* v_as_3176_, lean_object* v_as_x27_3177_, lean_object* v_b_3178_, lean_object* v_a_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v_as_x27_3177_, v_b_3178_, v___y_3180_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(lean_object* v_as_3184_, lean_object* v_as_x27_3185_, lean_object* v_b_3186_, lean_object* v_a_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(v_as_3184_, v_as_x27_3185_, v_b_3186_, v_a_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_as_x27_3185_);
lean_dec(v_as_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_Linter_List_listVariablesLinter));
v___x_3194_ = l_Lean_Elab_Command_addLinter(v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
return v_res_3196_;
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
