// Lean compiler output
// Module: Lean.Elab.InfoTree.Main
// Imports: public import Init.Task public import Lean.Meta.PPGoal public import Lean.ReservedNameAction import Init.Data.Format.Macro
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Task_mapList___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(lean_object*);
static const lean_array_object l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Main"};
static const lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Elab.PartialContextInfo.mergeIntoOuter\?"};
static const lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Unexpected incomplete InfoTree context info."};
static const lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4;
static lean_once_cell_t l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_lctx___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_CustomInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[CustomInfo("};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CustomInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CustomInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_CustomInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")]"};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CustomInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CustomInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object*);
static const lean_closure_object l_Lean_Elab_instToFormatCustomInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_CustomInfo_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToFormatCustomInfo___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatCustomInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToFormatCustomInfo = (const lean_object*)&l_Lean_Elab_instToFormatCustomInfo___closed__0_value;
static const lean_ctor_object l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6;
static const lean_ctor_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9;
static const lean_array_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2;
static const lean_array_object l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "†"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "†!"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "[Term] "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "(isBinder := true) "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "<failed-to-infer-type>"};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__8_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_PartialTermInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[PartialTerm] @ "};
static const lean_object* l_Lean_Elab_PartialTermInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialTermInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_PartialTermInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value;
static const lean_ctor_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value)}};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value;
static const lean_string_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value;
static const lean_ctor_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value)}};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[Completion-Id] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CompletionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "[Completion-Dot] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_CompletionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[Completion] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CommandInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[Command] @ "};
static const lean_object* l_Lean_Elab_CommandInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CommandInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CommandInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CommandInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CommandInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CommandInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OptionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "[Option] "};
static const lean_object* l_Lean_Elab_OptionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_OptionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_OptionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_OptionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_OptionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_OptionInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorNameInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[ErrorName] "};
static const lean_object* l_Lean_Elab_ErrorNameInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ErrorNameInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ErrorNameInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "[Field] "};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__0;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__3;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__4;
static const lean_string_object l_Lean_Elab_ContextInfo_ppGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no goals"};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__5 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ContextInfo_ppGoals___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__5_value)}};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__6 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[Tactic] @ "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nbefore "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nafter "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_MacroExpansionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "[MacroExpansion]\n"};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_MacroExpansionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_MacroExpansionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_MacroExpansionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__0;
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__1;
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__2;
static const lean_string_object l_Lean_Elab_UserWidgetInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[UserWidget] "};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__3_value;
static const lean_ctor_object l_Lean_Elab_UserWidgetInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__3_value)}};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_FVarAliasInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[FVarAlias] "};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FVarAliasInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_FVarAliasInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_FVarAliasInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_FieldRedeclInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[FieldRedecl] @ "};
static const lean_object* l_Lean_Elab_FieldRedeclInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FieldRedeclInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_FieldRedeclInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "[Error: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "[DelabTerm] @ "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nLocation: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nDocstring: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__5_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nExplicit: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__6 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__6_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__6_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__7 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__7_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__8 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__8_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__9 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ChoiceInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[Choice] @ "};
static const lean_object* l_Lean_Elab_ChoiceInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ChoiceInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ChoiceInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[Doc] "};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocElabInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "[DocElab] "};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocElabInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_DocElabInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_DocElabInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_DocElabInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ") @ "};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_DocElabInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialContextInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parent["};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__2_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "autoImplicits["};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 25, .m_data = "• <context-not-available>"};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__1_value;
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__2 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__3 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__3_value;
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "• \?"};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__4 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__5 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_getResetInfoTrees___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getResetInfoTrees___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withInfoContext_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.assignInfoHoleId"};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "assertion violation: ( __do_lift._@.Lean.Elab.InfoTree.Main.2379084842._hygCtx._hyg.19.0 ).isNone\n  "};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withEnableInfoTree___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0(lean_object* v_____do__lift_1_, lean_object* v_____do__lift_2_, lean_object* v_____do__lift_3_, lean_object* v_____do__lift_4_, lean_object* v_____do__lift_5_, lean_object* v_toPure_6_, lean_object* v_____do__lift_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_instInhabitedFileMap_default;
v___x_10_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_10_, 0, v_____do__lift_1_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_9_);
lean_ctor_set(v___x_10_, 3, v_____do__lift_2_);
lean_ctor_set(v___x_10_, 4, v_____do__lift_3_);
lean_ctor_set(v___x_10_, 5, v_____do__lift_4_);
lean_ctor_set(v___x_10_, 6, v_____do__lift_5_);
lean_ctor_set(v___x_10_, 7, v_____do__lift_7_);
v___x_11_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1(lean_object* v_inst_12_, lean_object* v_____do__lift_13_, lean_object* v_____do__lift_14_, lean_object* v_____do__lift_15_, lean_object* v_____do__lift_16_, lean_object* v_toPure_17_, lean_object* v_toBind_18_, lean_object* v_____do__lift_19_){
_start:
{
lean_object* v_getNGen_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v_getNGen_20_ = lean_ctor_get(v_inst_12_, 0);
lean_inc(v_getNGen_20_);
lean_dec_ref(v_inst_12_);
v___f_21_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0), 7, 6);
lean_closure_set(v___f_21_, 0, v_____do__lift_13_);
lean_closure_set(v___f_21_, 1, v_____do__lift_14_);
lean_closure_set(v___f_21_, 2, v_____do__lift_15_);
lean_closure_set(v___f_21_, 3, v_____do__lift_16_);
lean_closure_set(v___f_21_, 4, v_____do__lift_19_);
lean_closure_set(v___f_21_, 5, v_toPure_17_);
v___x_22_ = lean_apply_4(v_toBind_18_, lean_box(0), lean_box(0), v_getNGen_20_, v___f_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2(lean_object* v_inst_23_, lean_object* v_____do__lift_24_, lean_object* v_____do__lift_25_, lean_object* v_____do__lift_26_, lean_object* v_toPure_27_, lean_object* v_toBind_28_, lean_object* v_getOpenDecls_29_, lean_object* v_____do__lift_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
lean_inc(v_toBind_28_);
v___f_31_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1), 8, 7);
lean_closure_set(v___f_31_, 0, v_inst_23_);
lean_closure_set(v___f_31_, 1, v_____do__lift_24_);
lean_closure_set(v___f_31_, 2, v_____do__lift_25_);
lean_closure_set(v___f_31_, 3, v_____do__lift_26_);
lean_closure_set(v___f_31_, 4, v_____do__lift_30_);
lean_closure_set(v___f_31_, 5, v_toPure_27_);
lean_closure_set(v___f_31_, 6, v_toBind_28_);
v___x_32_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v_getOpenDecls_29_, v___f_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_____do__lift_35_, lean_object* v_____do__lift_36_, lean_object* v_toPure_37_, lean_object* v_toBind_38_, lean_object* v_____do__lift_39_){
_start:
{
lean_object* v_getCurrNamespace_40_; lean_object* v_getOpenDecls_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v_getCurrNamespace_40_ = lean_ctor_get(v_inst_33_, 0);
lean_inc(v_getCurrNamespace_40_);
v_getOpenDecls_41_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_getOpenDecls_41_);
lean_dec_ref(v_inst_33_);
lean_inc(v_toBind_38_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2), 8, 7);
lean_closure_set(v___f_42_, 0, v_inst_34_);
lean_closure_set(v___f_42_, 1, v_____do__lift_35_);
lean_closure_set(v___f_42_, 2, v_____do__lift_36_);
lean_closure_set(v___f_42_, 3, v_____do__lift_39_);
lean_closure_set(v___f_42_, 4, v_toPure_37_);
lean_closure_set(v___f_42_, 5, v_toBind_38_);
lean_closure_set(v___f_42_, 6, v_getOpenDecls_41_);
v___x_43_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v_getCurrNamespace_40_, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_____do__lift_46_, lean_object* v_toPure_47_, lean_object* v_toBind_48_, lean_object* v_inst_49_, lean_object* v_____do__lift_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_52_; 
lean_inc(v_toBind_48_);
v___f_51_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3), 7, 6);
lean_closure_set(v___f_51_, 0, v_inst_44_);
lean_closure_set(v___f_51_, 1, v_inst_45_);
lean_closure_set(v___f_51_, 2, v_____do__lift_46_);
lean_closure_set(v___f_51_, 3, v_____do__lift_50_);
lean_closure_set(v___f_51_, 4, v_toPure_47_);
lean_closure_set(v___f_51_, 5, v_toBind_48_);
v___x_52_ = lean_apply_4(v_toBind_48_, lean_box(0), lean_box(0), v_inst_49_, v___f_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_toPure_56_, lean_object* v_toBind_57_, lean_object* v_inst_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v_getMCtx_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v_getMCtx_60_ = lean_ctor_get(v_inst_53_, 0);
lean_inc(v_getMCtx_60_);
lean_dec_ref(v_inst_53_);
lean_inc(v_toBind_57_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4), 7, 6);
lean_closure_set(v___f_61_, 0, v_inst_54_);
lean_closure_set(v___f_61_, 1, v_inst_55_);
lean_closure_set(v___f_61_, 2, v_____do__lift_59_);
lean_closure_set(v___f_61_, 3, v_toPure_56_);
lean_closure_set(v___f_61_, 4, v_toBind_57_);
lean_closure_set(v___f_61_, 5, v_inst_58_);
v___x_62_ = lean_apply_4(v_toBind_57_, lean_box(0), lean_box(0), v_getMCtx_60_, v___f_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v_toApplicative_69_; lean_object* v_toBind_70_; lean_object* v_getEnv_71_; lean_object* v_toPure_72_; lean_object* v___f_73_; lean_object* v___x_74_; 
v_toApplicative_69_ = lean_ctor_get(v_inst_63_, 0);
lean_inc_ref(v_toApplicative_69_);
v_toBind_70_ = lean_ctor_get(v_inst_63_, 1);
lean_inc_n(v_toBind_70_, 2);
lean_dec_ref(v_inst_63_);
v_getEnv_71_ = lean_ctor_get(v_inst_64_, 0);
lean_inc(v_getEnv_71_);
lean_dec_ref(v_inst_64_);
v_toPure_72_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_72_);
lean_dec_ref(v_toApplicative_69_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5), 7, 6);
lean_closure_set(v___f_73_, 0, v_inst_65_);
lean_closure_set(v___f_73_, 1, v_inst_67_);
lean_closure_set(v___f_73_, 2, v_inst_68_);
lean_closure_set(v___f_73_, 3, v_toPure_72_);
lean_closure_set(v___f_73_, 4, v_toBind_70_);
lean_closure_set(v___f_73_, 5, v_inst_66_);
v___x_74_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_getEnv_71_, v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap(lean_object* v_m_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_inst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(lean_object* v_ctx_83_, lean_object* v_toPure_84_, lean_object* v_____do__lift_85_){
_start:
{
lean_object* v_env_86_; lean_object* v_cmdEnv_x3f_87_; lean_object* v_mctx_88_; lean_object* v_options_89_; lean_object* v_currNamespace_90_; lean_object* v_openDecls_91_; lean_object* v_ngen_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_env_86_ = lean_ctor_get(v_ctx_83_, 0);
v_cmdEnv_x3f_87_ = lean_ctor_get(v_ctx_83_, 1);
v_mctx_88_ = lean_ctor_get(v_ctx_83_, 3);
v_options_89_ = lean_ctor_get(v_ctx_83_, 4);
v_currNamespace_90_ = lean_ctor_get(v_ctx_83_, 5);
v_openDecls_91_ = lean_ctor_get(v_ctx_83_, 6);
v_ngen_92_ = lean_ctor_get(v_ctx_83_, 7);
v_isSharedCheck_100_ = !lean_is_exclusive(v_ctx_83_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_ctx_83_, 2);
lean_dec(v_unused_101_);
v___x_94_ = v_ctx_83_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_ngen_92_);
lean_inc(v_openDecls_91_);
lean_inc(v_currNamespace_90_);
lean_inc(v_options_89_);
lean_inc(v_mctx_88_);
lean_inc(v_cmdEnv_x3f_87_);
lean_inc(v_env_86_);
lean_dec(v_ctx_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v_____do__lift_85_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_cmdEnv_x3f_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_____do__lift_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_mctx_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_options_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_currNamespace_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_openDecls_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_ngen_92_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(lean_object* v_toPure_102_, lean_object* v_toBind_103_, lean_object* v_inst_104_, lean_object* v_ctx_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__0), 3, 2);
lean_closure_set(v___f_106_, 0, v_ctx_105_);
lean_closure_set(v___f_106_, 1, v_toPure_102_);
v___x_107_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v_inst_104_, v___f_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_116_ = lean_ctor_get(v_inst_108_, 1);
lean_inc_n(v_toBind_116_, 2);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_toPure_117_);
v___x_118_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__1), 4, 3);
lean_closure_set(v___f_119_, 0, v_toPure_117_);
lean_closure_set(v___f_119_, 1, v_toBind_116_);
lean_closure_set(v___f_119_, 2, v_inst_114_);
v___x_120_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_118_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save(lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_inst_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(lean_object* v_msg_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(0);
v___x_132_ = lean_panic_fn_borrowed(v___x_131_, v_msg_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3));
v___x_139_ = lean_unsigned_to_nat(4u);
v___x_140_ = lean_unsigned_to_nat(52u);
v___x_141_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2));
v___x_142_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_143_ = l_mkPanicMessageWithDecl(v___x_142_, v___x_141_, v___x_140_, v___x_139_, v___x_138_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3));
v___x_145_ = lean_unsigned_to_nat(4u);
v___x_146_ = lean_unsigned_to_nat(54u);
v___x_147_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2));
v___x_148_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_149_ = l_mkPanicMessageWithDecl(v___x_148_, v___x_147_, v___x_146_, v___x_145_, v___x_144_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
switch(lean_obj_tag(v_x_150_))
{
case 0:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v_info_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_162_; 
v_info_152_ = lean_ctor_get(v_x_150_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_162_ == 0)
{
v___x_154_ = v_x_150_;
v_isShared_155_ = v_isSharedCheck_162_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_info_152_);
lean_dec(v_x_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_162_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_156_ = lean_box(0);
v___x_157_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0));
v___x_158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_158_, 0, v_info_152_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 0, v___x_158_);
v___x_160_ = v___x_154_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v_info_163_; lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_199_; 
v_info_163_ = lean_ctor_get(v_x_150_, 0);
lean_inc_ref(v_info_163_);
lean_dec_ref_known(v_x_150_, 1);
v_val_164_ = lean_ctor_get(v_x_151_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_199_ == 0)
{
v___x_166_ = v_x_151_;
v_isShared_167_ = v_isSharedCheck_199_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_dec(v_x_151_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_199_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_env_168_; lean_object* v_cmdEnv_x3f_169_; lean_object* v_fileMap_170_; lean_object* v_mctx_171_; lean_object* v_options_172_; lean_object* v_currNamespace_173_; lean_object* v_openDecls_174_; lean_object* v_ngen_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_198_; 
v_env_168_ = lean_ctor_get(v_info_163_, 0);
v_cmdEnv_x3f_169_ = lean_ctor_get(v_info_163_, 1);
v_fileMap_170_ = lean_ctor_get(v_info_163_, 2);
v_mctx_171_ = lean_ctor_get(v_info_163_, 3);
v_options_172_ = lean_ctor_get(v_info_163_, 4);
v_currNamespace_173_ = lean_ctor_get(v_info_163_, 5);
v_openDecls_174_ = lean_ctor_get(v_info_163_, 6);
v_ngen_175_ = lean_ctor_get(v_info_163_, 7);
v_isSharedCheck_198_ = !lean_is_exclusive(v_info_163_);
if (v_isSharedCheck_198_ == 0)
{
v___x_177_ = v_info_163_;
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_ngen_175_);
lean_inc(v_openDecls_174_);
lean_inc(v_currNamespace_173_);
lean_inc(v_options_172_);
lean_inc(v_mctx_171_);
lean_inc(v_fileMap_170_);
lean_inc(v_cmdEnv_x3f_169_);
lean_inc(v_env_168_);
lean_dec(v_info_163_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_toCommandContextInfo_179_; lean_object* v_parentDecl_x3f_180_; lean_object* v_autoImplicits_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_197_; 
v_toCommandContextInfo_179_ = lean_ctor_get(v_val_164_, 0);
v_parentDecl_x3f_180_ = lean_ctor_get(v_val_164_, 1);
v_autoImplicits_181_ = lean_ctor_get(v_val_164_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_val_164_);
if (v_isSharedCheck_197_ == 0)
{
v___x_183_ = v_val_164_;
v_isShared_184_ = v_isSharedCheck_197_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_autoImplicits_181_);
lean_inc(v_parentDecl_x3f_180_);
lean_inc(v_toCommandContextInfo_179_);
lean_dec(v_val_164_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_197_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___y_186_; lean_object* v_cmdEnv_x3f_196_; 
v_cmdEnv_x3f_196_ = lean_ctor_get(v_toCommandContextInfo_179_, 1);
lean_inc(v_cmdEnv_x3f_196_);
lean_dec_ref(v_toCommandContextInfo_179_);
if (lean_obj_tag(v_cmdEnv_x3f_196_) == 0)
{
v___y_186_ = v_cmdEnv_x3f_169_;
goto v___jp_185_;
}
else
{
lean_dec(v_cmdEnv_x3f_169_);
v___y_186_ = v_cmdEnv_x3f_196_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___y_186_);
v___x_188_ = v___x_177_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_env_168_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___y_186_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_fileMap_170_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_mctx_171_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_options_172_);
lean_ctor_set(v_reuseFailAlloc_195_, 5, v_currNamespace_173_);
lean_ctor_set(v_reuseFailAlloc_195_, 6, v_openDecls_174_);
lean_ctor_set(v_reuseFailAlloc_195_, 7, v_ngen_175_);
v___x_188_ = v_reuseFailAlloc_195_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_188_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_parentDecl_x3f_180_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_autoImplicits_181_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_190_);
v___x_192_ = v___x_166_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
}
case 1:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref_known(v_x_150_, 1);
v___x_200_ = lean_obj_once(&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4, &l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4_once, _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4);
v___x_201_ = l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_227_; 
v_val_202_ = lean_ctor_get(v_x_151_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_227_ == 0)
{
v___x_204_ = v_x_151_;
v_isShared_205_ = v_isSharedCheck_227_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_val_202_);
lean_dec(v_x_151_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_227_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_parentDecl_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_226_; 
v_parentDecl_206_ = lean_ctor_get(v_x_150_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_226_ == 0)
{
v___x_208_ = v_x_150_;
v_isShared_209_ = v_isSharedCheck_226_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_parentDecl_206_);
lean_dec(v_x_150_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_226_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_toCommandContextInfo_210_; lean_object* v_autoImplicits_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_224_; 
v_toCommandContextInfo_210_ = lean_ctor_get(v_val_202_, 0);
v_autoImplicits_211_ = lean_ctor_get(v_val_202_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_val_202_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v_val_202_, 1);
lean_dec(v_unused_225_);
v___x_213_ = v_val_202_;
v_isShared_214_ = v_isSharedCheck_224_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_autoImplicits_211_);
lean_inc(v_toCommandContextInfo_210_);
lean_dec(v_val_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_224_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v_parentDecl_206_);
v___x_216_ = v___x_204_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_parentDecl_206_);
v___x_216_ = v_reuseFailAlloc_223_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_216_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_toCommandContextInfo_210_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_autoImplicits_211_);
v___x_218_ = v_reuseFailAlloc_222_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_218_);
v___x_220_ = v___x_208_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
}
}
default: 
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref_known(v_x_150_, 1);
v___x_228_ = lean_obj_once(&l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5, &l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5_once, _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5);
v___x_229_ = l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_248_; 
v_val_230_ = lean_ctor_get(v_x_151_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_248_ == 0)
{
v___x_232_ = v_x_151_;
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_dec(v_x_151_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_autoImplicits_234_; lean_object* v_toCommandContextInfo_235_; lean_object* v_parentDecl_x3f_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_246_; 
v_autoImplicits_234_ = lean_ctor_get(v_x_150_, 0);
lean_inc_ref(v_autoImplicits_234_);
lean_dec_ref_known(v_x_150_, 1);
v_toCommandContextInfo_235_ = lean_ctor_get(v_val_230_, 0);
v_parentDecl_x3f_236_ = lean_ctor_get(v_val_230_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_val_230_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v_val_230_, 2);
lean_dec(v_unused_247_);
v___x_238_ = v_val_230_;
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_parentDecl_x3f_236_);
lean_inc(v_toCommandContextInfo_235_);
lean_dec(v_val_230_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 2, v_autoImplicits_234_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_toCommandContextInfo_235_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_parentDecl_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_autoImplicits_234_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_241_);
v___x_243_ = v___x_232_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_stx(lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_termInfo_250_; lean_object* v_toElabInfo_251_; lean_object* v_stx_252_; 
v_termInfo_250_ = lean_ctor_get(v_x_249_, 0);
v_toElabInfo_251_ = lean_ctor_get(v_termInfo_250_, 0);
v_stx_252_ = lean_ctor_get(v_toElabInfo_251_, 1);
lean_inc(v_stx_252_);
return v_stx_252_;
}
else
{
lean_object* v_stx_253_; 
v_stx_253_ = lean_ctor_get(v_x_249_, 0);
lean_inc(v_stx_253_);
return v_stx_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_stx___boxed(lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_CompletionInfo_stx(v_x_254_);
lean_dec_ref(v_x_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object* v_x_256_){
_start:
{
switch(lean_obj_tag(v_x_256_))
{
case 0:
{
lean_object* v_termInfo_257_; lean_object* v_lctx_258_; 
v_termInfo_257_ = lean_ctor_get(v_x_256_, 0);
v_lctx_258_ = lean_ctor_get(v_termInfo_257_, 1);
lean_inc_ref(v_lctx_258_);
return v_lctx_258_;
}
case 1:
{
lean_object* v_lctx_259_; 
v_lctx_259_ = lean_ctor_get(v_x_256_, 2);
lean_inc_ref(v_lctx_259_);
return v_lctx_259_;
}
case 2:
{
lean_object* v_lctx_260_; 
v_lctx_260_ = lean_ctor_get(v_x_256_, 2);
lean_inc_ref(v_lctx_260_);
return v_lctx_260_;
}
case 3:
{
lean_object* v_lctx_261_; 
v_lctx_261_ = lean_ctor_get(v_x_256_, 2);
lean_inc_ref(v_lctx_261_);
return v_lctx_261_;
}
default: 
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_LocalContext_empty;
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_lctx___boxed(lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Elab_CompletionInfo_lctx(v_x_263_);
lean_dec_ref(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object* v_x_271_){
_start:
{
lean_object* v_value_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_286_; 
v_value_272_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_x_271_, 0);
lean_dec(v_unused_287_);
v___x_274_ = v_x_271_;
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_value_272_);
lean_dec(v_x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__1));
v___x_277_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_272_);
lean_dec(v_value_272_);
v___x_278_ = 1;
v___x_279_ = l_Lean_Name_toString(v___x_277_, v___x_278_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
if (v_isShared_275_ == 0)
{
lean_ctor_set_tag(v___x_274_, 5);
lean_ctor_set(v___x_274_, 1, v___x_280_);
lean_ctor_set(v___x_274_, 0, v___x_276_);
v___x_282_ = v___x_274_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__3));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_p_293_, lean_object* v_as_294_, size_t v_sz_295_, size_t v_i_296_, lean_object* v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_lt(v_i_296_, v_sz_295_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_p_293_);
lean_inc_ref(v_b_297_);
return v_b_297_;
}
else
{
lean_object* v___x_299_; lean_object* v_a_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
v_a_300_ = lean_array_uget_borrowed(v_as_294_, v_i_296_);
lean_inc_ref(v_p_293_);
v___x_301_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_293_, v_a_300_);
if (lean_obj_tag(v___x_301_) == 1)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_p_293_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_299_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; 
lean_dec(v___x_301_);
v___x_304_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0));
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_296_, v___x_305_);
v_i_296_ = v___x_306_;
v_b_297_ = v___x_304_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(lean_object* v_p_308_, lean_object* v_as_309_, size_t v_sz_310_, size_t v_i_311_, lean_object* v_b_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_lt(v_i_311_, v_sz_310_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_p_308_);
lean_inc_ref(v_b_312_);
return v_b_312_;
}
else
{
lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_316_; 
v___x_314_ = lean_box(0);
v_a_315_ = lean_array_uget_borrowed(v_as_309_, v_i_311_);
lean_inc(v_a_315_);
lean_inc_ref(v_p_308_);
v___x_316_ = l_Lean_Elab_InfoTree_findInfo_x3f(v_p_308_, v_a_315_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec_ref(v_p_308_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_314_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; size_t v___x_320_; size_t v___x_321_; 
lean_dec(v___x_316_);
v___x_319_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0));
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_add(v_i_311_, v___x_320_);
v_i_311_ = v___x_321_;
v_b_312_ = v___x_319_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(lean_object* v_p_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_cs_325_; lean_object* v___x_326_; lean_object* v___x_327_; size_t v_sz_328_; size_t v___x_329_; lean_object* v___x_330_; lean_object* v_fst_331_; 
v_cs_325_ = lean_ctor_get(v_x_324_, 0);
v___x_326_ = lean_box(0);
v___x_327_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0));
v_sz_328_ = lean_array_size(v_cs_325_);
v___x_329_ = ((size_t)0ULL);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(v_p_323_, v_cs_325_, v_sz_328_, v___x_329_, v___x_327_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_fst_331_);
lean_dec_ref(v___x_330_);
if (lean_obj_tag(v_fst_331_) == 0)
{
return v___x_326_;
}
else
{
lean_object* v_val_332_; 
v_val_332_ = lean_ctor_get(v_fst_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_fst_331_, 1);
return v_val_332_;
}
}
else
{
lean_object* v_vs_333_; lean_object* v___x_334_; lean_object* v___x_335_; size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; lean_object* v_fst_339_; 
v_vs_333_ = lean_ctor_get(v_x_324_, 0);
v___x_334_ = lean_box(0);
v___x_335_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0));
v_sz_336_ = lean_array_size(v_vs_333_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_323_, v_vs_333_, v_sz_336_, v___x_337_, v___x_335_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_fst_339_);
lean_dec_ref(v___x_338_);
if (lean_obj_tag(v_fst_339_) == 0)
{
return v___x_334_;
}
else
{
lean_object* v_val_340_; 
v_val_340_ = lean_ctor_get(v_fst_339_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v_fst_339_, 1);
return v_val_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(lean_object* v_p_341_, lean_object* v_t_342_){
_start:
{
lean_object* v_root_343_; lean_object* v_tail_344_; lean_object* v___x_345_; 
v_root_343_ = lean_ctor_get(v_t_342_, 0);
v_tail_344_ = lean_ctor_get(v_t_342_, 1);
lean_inc_ref(v_p_341_);
v___x_345_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_341_, v_root_343_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v___x_346_; size_t v_sz_347_; size_t v___x_348_; lean_object* v___x_349_; lean_object* v_fst_350_; 
v___x_346_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0));
v_sz_347_ = lean_array_size(v_tail_344_);
v___x_348_ = ((size_t)0ULL);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_341_, v_tail_344_, v_sz_347_, v___x_348_, v___x_346_);
v_fst_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_fst_350_);
lean_dec_ref(v___x_349_);
if (lean_obj_tag(v_fst_350_) == 0)
{
return v___x_345_;
}
else
{
lean_object* v_val_351_; 
v_val_351_ = lean_ctor_get(v_fst_350_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_fst_350_, 1);
return v_val_351_;
}
}
else
{
lean_dec_ref(v_p_341_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object* v_p_352_, lean_object* v_t_353_){
_start:
{
switch(lean_obj_tag(v_t_353_))
{
case 0:
{
lean_object* v_t_354_; 
v_t_354_ = lean_ctor_get(v_t_353_, 1);
lean_inc_ref(v_t_354_);
lean_dec_ref_known(v_t_353_, 2);
v_t_353_ = v_t_354_;
goto _start;
}
case 1:
{
lean_object* v_i_356_; lean_object* v_children_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_i_356_ = lean_ctor_get(v_t_353_, 0);
lean_inc_ref_n(v_i_356_, 2);
v_children_357_ = lean_ctor_get(v_t_353_, 1);
lean_inc_ref(v_children_357_);
lean_dec_ref_known(v_t_353_, 2);
lean_inc_ref(v_p_352_);
v___x_358_ = lean_apply_1(v_p_352_, v_i_356_);
v___x_359_ = lean_unbox(v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec_ref(v_i_356_);
v___x_360_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(v_p_352_, v_children_357_);
lean_dec_ref(v_children_357_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
lean_dec_ref(v_children_357_);
lean_dec_ref(v_p_352_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_i_356_);
return v___x_361_;
}
}
default: 
{
lean_object* v___x_362_; 
lean_dec_ref(v_t_353_);
lean_dec_ref(v_p_352_);
v___x_362_ = lean_box(0);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___boxed(lean_object* v_p_363_, lean_object* v_t_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(v_p_363_, v_t_364_);
lean_dec_ref(v_t_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1___boxed(lean_object* v_p_366_, lean_object* v_as_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_b_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_372_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_366_, v_as_367_, v_sz_boxed_371_, v_i_boxed_372_, v_b_370_);
lean_dec_ref(v_b_370_);
lean_dec_ref(v_as_367_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_p_374_, lean_object* v_as_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_b_378_){
_start:
{
size_t v_sz_boxed_379_; size_t v_i_boxed_380_; lean_object* v_res_381_; 
v_sz_boxed_379_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_380_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(v_p_374_, v_as_375_, v_sz_boxed_379_, v_i_boxed_380_, v_b_378_);
lean_dec_ref(v_b_378_);
lean_dec_ref(v_as_375_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0___boxed(lean_object* v_p_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_382_, v_x_383_);
lean_dec_ref(v_x_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_k_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v_keys_385_);
v___x_390_ = lean_nat_dec_lt(v_i_387_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v_i_387_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v_k_x27_392_; uint8_t v___x_393_; 
v_k_x27_392_ = lean_array_fget_borrowed(v_keys_385_, v_i_387_);
v___x_393_ = l_Lean_instBEqMVarId_beq(v_k_388_, v_k_x27_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_i_387_, v___x_394_);
lean_dec(v_i_387_);
v_i_387_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_array_fget_borrowed(v_vals_386_, v_i_387_);
lean_dec(v_i_387_);
lean_inc(v___x_397_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_keys_399_, lean_object* v_vals_400_, lean_object* v_i_401_, lean_object* v_k_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_399_, v_vals_400_, v_i_401_, v_k_402_);
lean_dec(v_k_402_);
lean_dec_ref(v_vals_400_);
lean_dec_ref(v_keys_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(lean_object* v_x_404_, size_t v_x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v_es_407_; lean_object* v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v_j_411_; lean_object* v___x_412_; 
v_es_407_ = lean_ctor_get(v_x_404_, 0);
v___x_408_ = lean_box(2);
v___x_409_ = ((size_t)31ULL);
v___x_410_ = lean_usize_land(v_x_405_, v___x_409_);
v_j_411_ = lean_usize_to_nat(v___x_410_);
v___x_412_ = lean_array_get_borrowed(v___x_408_, v_es_407_, v_j_411_);
lean_dec(v_j_411_);
switch(lean_obj_tag(v___x_412_))
{
case 0:
{
lean_object* v_key_413_; lean_object* v_val_414_; uint8_t v___x_415_; 
v_key_413_ = lean_ctor_get(v___x_412_, 0);
v_val_414_ = lean_ctor_get(v___x_412_, 1);
v___x_415_ = l_Lean_instBEqMVarId_beq(v_x_406_, v_key_413_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_val_414_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_val_414_);
return v___x_417_;
}
}
case 1:
{
lean_object* v_node_418_; size_t v___x_419_; size_t v___x_420_; 
v_node_418_ = lean_ctor_get(v___x_412_, 0);
v___x_419_ = ((size_t)5ULL);
v___x_420_ = lean_usize_shift_right(v_x_405_, v___x_419_);
v_x_404_ = v_node_418_;
v_x_405_ = v___x_420_;
goto _start;
}
default: 
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_ks_423_ = lean_ctor_get(v_x_404_, 0);
v_vs_424_ = lean_ctor_get(v_x_404_, 1);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_ks_423_, v_vs_424_, v___x_425_, v_x_406_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_677__boxed_430_; lean_object* v_res_431_; 
v_x_677__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_427_, v_x_677__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_427_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint64_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_instHashableMVarId_hash(v_x_433_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_432_, v___x_435_, v_x_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg___boxed(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec_ref(v_x_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(lean_object* v_assignment_440_, size_t v_sz_441_, size_t v_i_442_, lean_object* v_bs_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_444_ == 0)
{
return v_bs_443_;
}
else
{
lean_object* v_v_445_; lean_object* v___x_446_; lean_object* v_bs_x27_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_445_ = lean_array_uget(v_bs_443_, v_i_442_);
v___x_446_ = lean_unsigned_to_nat(0u);
v_bs_x27_447_ = lean_array_uset(v_bs_443_, v_i_442_, v___x_446_);
v___x_448_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_440_, v_v_445_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_442_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_447_, v_i_442_, v___x_448_);
v_i_442_ = v___x_450_;
v_bs_443_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute(lean_object* v_tree_453_, lean_object* v_assignment_454_){
_start:
{
switch(lean_obj_tag(v_tree_453_))
{
case 0:
{
lean_object* v_i_455_; lean_object* v_t_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_i_455_ = lean_ctor_get(v_tree_453_, 0);
v_t_456_ = lean_ctor_get(v_tree_453_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_tree_453_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_tree_453_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_t_456_);
lean_inc(v_i_455_);
lean_dec(v_tree_453_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_Elab_InfoTree_substitute(v_t_456_, v_assignment_454_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_i_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
case 1:
{
lean_object* v_i_465_; lean_object* v_children_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_i_465_ = lean_ctor_get(v_tree_453_, 0);
v_children_466_ = lean_ctor_get(v_tree_453_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_tree_453_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v_tree_453_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_children_466_);
lean_inc(v_i_465_);
lean_dec(v_tree_453_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(v_assignment_454_, v_children_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_i_465_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
default: 
{
lean_object* v_mvarId_475_; lean_object* v___x_476_; 
v_mvarId_475_ = lean_ctor_get(v_tree_453_, 0);
v___x_476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_assignment_454_, v_mvarId_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
return v_tree_453_;
}
else
{
lean_object* v_val_477_; 
lean_dec_ref_known(v_tree_453_, 1);
v_val_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v___x_476_, 1);
v_tree_453_ = v_val_477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(lean_object* v_assignment_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_bs_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_483_ == 0)
{
return v_bs_482_;
}
else
{
lean_object* v_v_484_; lean_object* v___x_485_; lean_object* v_bs_x27_486_; lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v_v_484_ = lean_array_uget(v_bs_482_, v_i_481_);
v___x_485_ = lean_unsigned_to_nat(0u);
v_bs_x27_486_ = lean_array_uset(v_bs_482_, v_i_481_, v___x_485_);
v___x_487_ = l_Lean_Elab_InfoTree_substitute(v_v_484_, v_assignment_479_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_481_, v___x_488_);
v___x_490_ = lean_array_uset(v_bs_x27_486_, v_i_481_, v___x_487_);
v_i_481_ = v___x_489_;
v_bs_482_ = v___x_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(lean_object* v_assignment_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_cs_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_504_; 
v_cs_494_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_504_ == 0)
{
v___x_496_ = v_x_493_;
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_cs_494_);
lean_dec(v_x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
size_t v_sz_498_; size_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v_sz_498_ = lean_array_size(v_cs_494_);
v___x_499_ = ((size_t)0ULL);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_492_, v_sz_498_, v___x_499_, v_cs_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_500_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_vs_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_vs_505_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v_x_493_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_vs_505_);
lean_dec(v_x_493_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_sz_509_ = lean_array_size(v_vs_505_);
v___x_510_ = ((size_t)0ULL);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_492_, v_sz_509_, v___x_510_, v_vs_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(lean_object* v_assignment_516_, lean_object* v_t_517_){
_start:
{
lean_object* v_root_518_; lean_object* v_tail_519_; lean_object* v_size_520_; size_t v_shift_521_; lean_object* v_tailOff_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_root_518_ = lean_ctor_get(v_t_517_, 0);
v_tail_519_ = lean_ctor_get(v_t_517_, 1);
v_size_520_ = lean_ctor_get(v_t_517_, 2);
v_shift_521_ = lean_ctor_get_usize(v_t_517_, 4);
v_tailOff_522_ = lean_ctor_get(v_t_517_, 3);
v_isSharedCheck_533_ = !lean_is_exclusive(v_t_517_);
if (v_isSharedCheck_533_ == 0)
{
v___x_524_ = v_t_517_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_tailOff_522_);
lean_inc(v_size_520_);
lean_inc(v_tail_519_);
lean_inc(v_root_518_);
lean_dec(v_t_517_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_526_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_516_, v_root_518_);
v_sz_527_ = lean_array_size(v_tail_519_);
v___x_528_ = ((size_t)0ULL);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_516_, v_sz_527_, v___x_528_, v_tail_519_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_529_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_size_520_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_tailOff_522_);
lean_ctor_set_usize(v_reuseFailAlloc_532_, 4, v_shift_521_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0___boxed(lean_object* v_assignment_534_, lean_object* v_t_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(v_assignment_534_, v_t_535_);
lean_dec_ref(v_assignment_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0___boxed(lean_object* v_assignment_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_537_, v_x_538_);
lean_dec_ref(v_assignment_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1___boxed(lean_object* v_assignment_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_bs_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_540_, v_sz_boxed_544_, v_i_boxed_545_, v_bs_543_);
lean_dec_ref(v_assignment_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1___boxed(lean_object* v_assignment_547_, lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_547_, v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
lean_dec_ref(v_assignment_547_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute___boxed(lean_object* v_tree_554_, lean_object* v_assignment_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_InfoTree_substitute(v_tree_554_, v_assignment_555_);
lean_dec_ref(v_assignment_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___boxed(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(v_00_u03b2_561_, v_x_562_, v_x_563_);
lean_dec(v_x_563_);
lean_dec_ref(v_x_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(lean_object* v_00_u03b2_565_, lean_object* v_x_566_, size_t v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_566_, v_x_567_, v_x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___boxed(lean_object* v_00_u03b2_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
size_t v_x_883__boxed_574_; lean_object* v_res_575_; 
v_x_883__boxed_574_ = lean_unbox_usize(v_x_572_);
lean_dec(v_x_572_);
v_res_575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(v_00_u03b2_570_, v_x_571_, v_x_883__boxed_574_, v_x_573_);
lean_dec(v_x_573_);
lean_dec_ref(v_x_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_576_, lean_object* v_keys_577_, lean_object* v_vals_578_, lean_object* v_heq_579_, lean_object* v_i_580_, lean_object* v_k_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_577_, v_vals_578_, v_i_580_, v_k_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_583_, lean_object* v_keys_584_, lean_object* v_vals_585_, lean_object* v_heq_586_, lean_object* v_i_587_, lean_object* v_k_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(v_00_u03b2_583_, v_keys_584_, v_vals_585_, v_heq_586_, v_i_587_, v_k_588_);
lean_dec(v_k_588_);
lean_dec_ref(v_vals_585_);
lean_dec_ref(v_keys_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(lean_object* v_f_590_, lean_object* v_as_591_, lean_object* v_i_592_, lean_object* v_acc_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_get_size(v_as_591_);
v___x_595_ = lean_nat_dec_eq(v_i_592_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_596_ = lean_array_fget_borrowed(v_as_591_, v_i_592_);
lean_inc(v_f_590_);
lean_inc(v___x_596_);
v___x_597_ = lean_apply_1(v_f_590_, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_i_592_, v___x_598_);
lean_dec(v_i_592_);
v___x_600_ = lean_array_push(v_acc_593_, v___x_597_);
v_i_592_ = v___x_599_;
v_acc_593_ = v___x_600_;
goto _start;
}
else
{
lean_dec(v_i_592_);
lean_dec(v_f_590_);
return v_acc_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_f_602_, lean_object* v_as_603_, lean_object* v_i_604_, lean_object* v_acc_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_602_, v_as_603_, v_i_604_, v_acc_605_);
lean_dec_ref(v_as_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_607_, lean_object* v_as_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_array_get_size(v_as_608_);
v___x_611_ = lean_mk_empty_array_with_capacity(v___x_610_);
v___x_612_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_607_, v_as_608_, v___x_609_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_613_, lean_object* v_as_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_613_, v_as_614_);
lean_dec_ref(v_as_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_616_, size_t v_sz_617_, size_t v_i_618_, lean_object* v_bs_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_lt(v_i_618_, v_sz_617_);
if (v___x_620_ == 0)
{
lean_dec(v_f_616_);
return v_bs_619_;
}
else
{
lean_object* v_v_621_; lean_object* v___x_622_; lean_object* v_bs_x27_623_; lean_object* v___y_625_; 
v_v_621_ = lean_array_uget(v_bs_619_, v_i_618_);
v___x_622_ = lean_unsigned_to_nat(0u);
v_bs_x27_623_ = lean_array_uset(v_bs_619_, v_i_618_, v___x_622_);
switch(lean_obj_tag(v_v_621_))
{
case 0:
{
lean_object* v_key_630_; lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v_key_630_ = lean_ctor_get(v_v_621_, 0);
v_val_631_ = lean_ctor_get(v_v_621_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_v_621_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v_v_621_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_inc(v_key_630_);
lean_dec(v_v_621_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc(v_f_616_);
v___x_635_ = lean_apply_1(v_f_616_, v_val_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_key_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_625_ = v___x_637_;
goto v___jp_624_;
}
}
}
case 1:
{
lean_object* v_node_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_node_640_ = lean_ctor_get(v_v_621_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_v_621_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_v_621_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_node_640_);
lean_dec(v_v_621_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_inc(v_f_616_);
v___x_644_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_616_, v_node_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v___y_625_ = v___x_646_;
goto v___jp_624_;
}
}
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(2);
v___y_625_ = v___x_649_;
goto v___jp_624_;
}
}
v___jp_624_:
{
size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_618_, v___x_626_);
v___x_628_ = lean_array_uset(v_bs_x27_623_, v_i_618_, v___y_625_);
v_i_618_ = v___x_627_;
v_bs_619_ = v___x_628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(lean_object* v_f_650_, lean_object* v_n_651_){
_start:
{
if (lean_obj_tag(v_n_651_) == 0)
{
lean_object* v_es_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_662_; 
v_es_652_ = lean_ctor_get(v_n_651_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_n_651_);
if (v_isSharedCheck_662_ == 0)
{
v___x_654_ = v_n_651_;
v_isShared_655_ = v_isSharedCheck_662_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_es_652_);
lean_dec(v_n_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_662_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
size_t v_sz_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_sz_656_ = lean_array_size(v_es_652_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_650_, v_sz_656_, v___x_657_, v_es_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_658_);
v___x_660_ = v___x_654_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_ks_663_; lean_object* v_vs_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_ks_663_ = lean_ctor_get(v_n_651_, 0);
v_vs_664_ = lean_ctor_get(v_n_651_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_n_651_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_n_651_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_vs_664_);
lean_inc(v_ks_663_);
lean_dec(v_n_651_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_val_668_; lean_object* v___x_670_; 
v_val_668_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_650_, v_vs_664_);
lean_dec_ref(v_vs_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_val_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_ks_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_val_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_bs_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_673_, v_sz_boxed_677_, v_i_boxed_678_, v_bs_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0(lean_object* v_f_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_apply_1(v_f_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(lean_object* v_pm_683_, lean_object* v_f_684_){
_start:
{
lean_object* v___f_685_; lean_object* v___x_686_; 
v___f_685_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_685_, 0, v_f_684_);
v___x_686_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v___f_685_, v_pm_683_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0(lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_task_get_own(v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(lean_object* v_s_690_, size_t v_sz_691_, size_t v_i_692_, lean_object* v_bs_693_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_lt(v_i_692_, v_sz_691_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_s_690_);
return v_bs_693_;
}
else
{
lean_object* v_lazyAssignment_695_; lean_object* v_v_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v_bs_x27_699_; lean_object* v___x_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v_lazyAssignment_695_ = lean_ctor_get(v_s_690_, 1);
v_v_696_ = lean_array_uget(v_bs_693_, v_i_692_);
v___f_697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0));
v___x_698_ = lean_unsigned_to_nat(0u);
v_bs_x27_699_ = lean_array_uset(v_bs_693_, v_i_692_, v___x_698_);
lean_inc_ref(v_lazyAssignment_695_);
v___x_700_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_lazyAssignment_695_, v___f_697_);
v___x_701_ = l_Lean_Elab_InfoTree_substitute(v_v_696_, v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_i_692_, v___x_702_);
v___x_704_ = lean_array_uset(v_bs_x27_699_, v_i_692_, v___x_701_);
v_i_692_ = v___x_703_;
v_bs_693_ = v___x_704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___boxed(lean_object* v_s_706_, lean_object* v_sz_707_, lean_object* v_i_708_, lean_object* v_bs_709_){
_start:
{
size_t v_sz_boxed_710_; size_t v_i_boxed_711_; lean_object* v_res_712_; 
v_sz_boxed_710_ = lean_unbox_usize(v_sz_707_);
lean_dec(v_sz_707_);
v_i_boxed_711_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_706_, v_sz_boxed_710_, v_i_boxed_711_, v_bs_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(lean_object* v_s_713_, size_t v_sz_714_, size_t v_i_715_, lean_object* v_bs_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_lt(v_i_715_, v_sz_714_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_s_713_);
return v_bs_716_;
}
else
{
lean_object* v_v_718_; lean_object* v___x_719_; lean_object* v_bs_x27_720_; lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v_v_718_ = lean_array_uget(v_bs_716_, v_i_715_);
v___x_719_ = lean_unsigned_to_nat(0u);
v_bs_x27_720_ = lean_array_uset(v_bs_716_, v_i_715_, v___x_719_);
lean_inc_ref(v_s_713_);
v___x_721_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_713_, v_v_718_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_715_, v___x_722_);
v___x_724_ = lean_array_uset(v_bs_x27_720_, v_i_715_, v___x_721_);
v_i_715_ = v___x_723_;
v_bs_716_ = v___x_724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(lean_object* v_s_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v_cs_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
v_cs_728_ = lean_ctor_get(v_x_727_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_738_ == 0)
{
v___x_730_ = v_x_727_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_cs_728_);
lean_dec(v_x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
size_t v_sz_732_; size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_sz_732_ = lean_array_size(v_cs_728_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_726_, v_sz_732_, v___x_733_, v_cs_728_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_vs_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_749_; 
v_vs_739_ = lean_ctor_get(v_x_727_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_749_ == 0)
{
v___x_741_ = v_x_727_;
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_vs_739_);
lean_dec(v_x_727_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v_sz_743_ = lean_array_size(v_vs_739_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_726_, v_sz_743_, v___x_744_, v_vs_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_745_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4___boxed(lean_object* v_s_750_, lean_object* v_sz_751_, lean_object* v_i_752_, lean_object* v_bs_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_751_);
lean_dec(v_sz_751_);
v_i_boxed_755_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_750_, v_sz_boxed_754_, v_i_boxed_755_, v_bs_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(lean_object* v_s_757_, lean_object* v_t_758_){
_start:
{
lean_object* v_root_759_; lean_object* v_tail_760_; lean_object* v_size_761_; size_t v_shift_762_; lean_object* v_tailOff_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_774_; 
v_root_759_ = lean_ctor_get(v_t_758_, 0);
v_tail_760_ = lean_ctor_get(v_t_758_, 1);
v_size_761_ = lean_ctor_get(v_t_758_, 2);
v_shift_762_ = lean_ctor_get_usize(v_t_758_, 4);
v_tailOff_763_ = lean_ctor_get(v_t_758_, 3);
v_isSharedCheck_774_ = !lean_is_exclusive(v_t_758_);
if (v_isSharedCheck_774_ == 0)
{
v___x_765_ = v_t_758_;
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tailOff_763_);
lean_inc(v_size_761_);
lean_inc(v_tail_760_);
lean_inc(v_root_759_);
lean_dec(v_t_758_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc_ref(v_s_757_);
v___x_767_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_757_, v_root_759_);
v_sz_768_ = lean_array_size(v_tail_760_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_757_, v_sz_768_, v___x_769_, v_tail_760_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_770_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_size_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_tailOff_763_);
lean_ctor_set_usize(v_reuseFailAlloc_773_, 4, v_shift_762_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0(lean_object* v_s_778_, lean_object* v_trees_779_, uint8_t v_enabled_780_, lean_object* v_assignment_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1);
v___x_784_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(v_s_778_, v_trees_779_);
v___x_785_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_785_, 0, v_assignment_781_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*3, v_enabled_780_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed(lean_object* v_s_786_, lean_object* v_trees_787_, lean_object* v_enabled_788_, lean_object* v_assignment_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_enabled_boxed_791_; lean_object* v_res_792_; 
v_enabled_boxed_791_ = lean_unbox(v_enabled_788_);
v_res_792_ = l_Lean_Elab_InfoState_substituteLazy___lam__0(v_s_786_, v_trees_787_, v_enabled_boxed_791_, v_assignment_789_, v_x_790_);
lean_dec(v_x_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0(lean_object* v_f_793_, lean_object* v_x1_794_, lean_object* v_x2_795_, lean_object* v_x3_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_apply_3(v_f_793_, v_x1_794_, v_x2_795_, v_x3_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_f_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_i_801_, lean_object* v_acc_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_keys_799_);
v___x_804_ = lean_nat_dec_lt(v_i_801_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v_i_801_);
lean_dec(v_f_798_);
return v_acc_802_;
}
else
{
lean_object* v_k_805_; lean_object* v_v_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_k_805_ = lean_array_fget_borrowed(v_keys_799_, v_i_801_);
v_v_806_ = lean_array_fget_borrowed(v_vals_800_, v_i_801_);
lean_inc(v_f_798_);
lean_inc(v_v_806_);
lean_inc(v_k_805_);
v___x_807_ = lean_apply_3(v_f_798_, v_acc_802_, v_k_805_, v_v_806_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_add(v_i_801_, v___x_808_);
lean_dec(v_i_801_);
v_i_801_ = v___x_809_;
v_acc_802_ = v___x_807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_f_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_i_814_, lean_object* v_acc_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_811_, v_keys_812_, v_vals_813_, v_i_814_, v_acc_815_);
lean_dec_ref(v_vals_813_);
lean_dec_ref(v_keys_812_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_f_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v_es_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_es_820_ = lean_ctor_get(v_x_818_, 0);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_array_get_size(v_es_820_);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v_f_817_);
return v_x_819_;
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_le(v___x_822_, v___x_822_);
if (v___x_824_ == 0)
{
if (v___x_823_ == 0)
{
lean_dec(v_f_817_);
return v_x_819_;
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_822_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_817_, v_es_820_, v___x_825_, v___x_826_, v_x_819_);
return v___x_827_;
}
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_822_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_817_, v_es_820_, v___x_828_, v___x_829_, v_x_819_);
return v___x_830_;
}
}
}
else
{
lean_object* v_ks_831_; lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_ks_831_ = lean_ctor_get(v_x_818_, 0);
v_vs_832_ = lean_ctor_get(v_x_818_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_817_, v_ks_831_, v_vs_832_, v___x_833_, v_x_819_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(lean_object* v_f_835_, lean_object* v_as_836_, size_t v_i_837_, size_t v_stop_838_, lean_object* v_b_839_){
_start:
{
lean_object* v___y_841_; uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_eq(v_i_837_, v_stop_838_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
v___x_846_ = lean_array_uget_borrowed(v_as_836_, v_i_837_);
switch(lean_obj_tag(v___x_846_))
{
case 0:
{
lean_object* v_key_847_; lean_object* v_val_848_; lean_object* v___x_849_; 
v_key_847_ = lean_ctor_get(v___x_846_, 0);
v_val_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_f_835_);
lean_inc(v_val_848_);
lean_inc(v_key_847_);
v___x_849_ = lean_apply_3(v_f_835_, v_b_839_, v_key_847_, v_val_848_);
v___y_841_ = v___x_849_;
goto v___jp_840_;
}
case 1:
{
lean_object* v_node_850_; lean_object* v___x_851_; 
v_node_850_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_f_835_);
v___x_851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_835_, v_node_850_, v_b_839_);
v___y_841_ = v___x_851_;
goto v___jp_840_;
}
default: 
{
v___y_841_ = v_b_839_;
goto v___jp_840_;
}
}
}
else
{
lean_dec(v_f_835_);
return v_b_839_;
}
v___jp_840_:
{
size_t v___x_842_; size_t v___x_843_; 
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_837_, v___x_842_);
v_i_837_ = v___x_843_;
v_b_839_ = v___y_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg___boxed(lean_object* v_f_852_, lean_object* v_as_853_, lean_object* v_i_854_, lean_object* v_stop_855_, lean_object* v_b_856_){
_start:
{
size_t v_i_boxed_857_; size_t v_stop_boxed_858_; lean_object* v_res_859_; 
v_i_boxed_857_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_stop_boxed_858_ = lean_unbox_usize(v_stop_855_);
lean_dec(v_stop_855_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_852_, v_as_853_, v_i_boxed_857_, v_stop_boxed_858_, v_b_856_);
lean_dec_ref(v_as_853_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_f_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_860_, v_x_861_, v_x_862_);
lean_dec_ref(v_x_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(lean_object* v_map_864_, lean_object* v_f_865_, lean_object* v_init_866_){
_start:
{
lean_object* v___f_867_; lean_object* v___x_868_; 
v___f_867_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0), 4, 1);
lean_closure_set(v___f_867_, 0, v_f_865_);
v___x_868_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v___f_867_, v_map_864_, v_init_866_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___boxed(lean_object* v_map_869_, lean_object* v_f_870_, lean_object* v_init_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_869_, v_f_870_, v_init_871_);
lean_dec_ref(v_map_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0(lean_object* v_ps_873_, lean_object* v_k_874_, lean_object* v_v_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_k_874_);
lean_ctor_set(v___x_876_, 1, v_v_875_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v_ps_873_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(lean_object* v_m_879_){
_start:
{
lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___f_880_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0));
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_m_879_, v___f_880_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___boxed(lean_object* v_m_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_883_);
lean_dec_ref(v_m_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
if (lean_obj_tag(v_a_885_) == 0)
{
lean_object* v___x_887_; 
v___x_887_ = l_List_reverse___redArg(v_a_886_);
return v___x_887_;
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
v_head_888_ = lean_ctor_get(v_a_885_, 0);
v_tail_889_ = lean_ctor_get(v_a_885_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_898_ == 0)
{
v___x_891_ = v_a_885_;
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_tail_889_);
lean_inc(v_head_888_);
lean_dec(v_a_885_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_snd_893_; lean_object* v___x_895_; 
v_snd_893_ = lean_ctor_get(v_head_888_, 1);
lean_inc(v_snd_893_);
lean_dec(v_head_888_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_a_886_);
lean_ctor_set(v___x_891_, 0, v_snd_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_snd_893_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_886_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v_a_885_ = v_tail_889_;
v_a_886_ = v___x_895_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object* v_s_899_){
_start:
{
uint8_t v_enabled_900_; lean_object* v_assignment_901_; lean_object* v_lazyAssignment_902_; lean_object* v_trees_903_; lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v_enabled_900_ = lean_ctor_get_uint8(v_s_899_, sizeof(void*)*3);
v_assignment_901_ = lean_ctor_get(v_s_899_, 0);
lean_inc_ref(v_assignment_901_);
v_lazyAssignment_902_ = lean_ctor_get(v_s_899_, 1);
lean_inc_ref(v_lazyAssignment_902_);
v_trees_903_ = lean_ctor_get(v_s_899_, 2);
lean_inc_ref(v_trees_903_);
v___x_904_ = lean_box(v_enabled_900_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed), 5, 4);
lean_closure_set(v___f_905_, 0, v_s_899_);
lean_closure_set(v___f_905_, 1, v_trees_903_);
lean_closure_set(v___f_905_, 2, v___x_904_);
lean_closure_set(v___f_905_, 3, v_assignment_901_);
v___x_906_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_lazyAssignment_902_);
lean_dec_ref(v_lazyAssignment_902_);
v___x_907_ = lean_box(0);
v___x_908_ = l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(v___x_906_, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = 0;
v___x_911_ = l_Task_mapList___redArg(v___f_905_, v___x_908_, v___x_909_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0(lean_object* v_00_u03b2_912_, lean_object* v_00_u03c3_913_, lean_object* v_pm_914_, lean_object* v_f_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_pm_914_, v_f_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(lean_object* v_00_u03b2_917_, lean_object* v_m_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___boxed(lean_object* v_00_u03b2_920_, lean_object* v_m_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(v_00_u03b2_920_, v_m_921_);
lean_dec_ref(v_m_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0___redArg(lean_object* v_pm_923_, lean_object* v_f_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_924_, v_pm_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0(lean_object* v_00_u03b2_926_, lean_object* v_00_u03c3_927_, lean_object* v_pm_928_, lean_object* v_f_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_929_, v_pm_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(lean_object* v_00_u03c3_931_, lean_object* v_00_u03b2_932_, lean_object* v_map_933_, lean_object* v_f_934_, lean_object* v_init_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_933_, v_f_934_, v_init_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___boxed(lean_object* v_00_u03c3_937_, lean_object* v_00_u03b2_938_, lean_object* v_map_939_, lean_object* v_f_940_, lean_object* v_init_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(v_00_u03c3_937_, v_00_u03b2_938_, v_map_939_, v_f_940_, v_init_941_);
lean_dec_ref(v_map_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_00_u03c3_945_, lean_object* v_f_946_, lean_object* v_n_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_946_, v_n_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(lean_object* v_map_949_, lean_object* v_f_950_, lean_object* v_init_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_950_, v_map_949_, v_init_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_map_953_, lean_object* v_f_954_, lean_object* v_init_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(v_map_953_, v_f_954_, v_init_955_);
lean_dec_ref(v_map_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_957_, lean_object* v_00_u03b2_958_, lean_object* v_map_959_, lean_object* v_f_960_, lean_object* v_init_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_960_, v_map_959_, v_init_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_963_, lean_object* v_00_u03b2_964_, lean_object* v_map_965_, lean_object* v_f_966_, lean_object* v_init_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(v_00_u03c3_963_, v_00_u03b2_964_, v_map_965_, v_f_966_, v_init_967_);
lean_dec_ref(v_map_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_00_u03c3_971_, lean_object* v_f_972_, size_t v_sz_973_, size_t v_i_974_, lean_object* v_bs_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_972_, v_sz_973_, v_i_974_, v_bs_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_00_u03c3_979_, lean_object* v_f_980_, lean_object* v_sz_981_, lean_object* v_i_982_, lean_object* v_bs_983_){
_start:
{
size_t v_sz_boxed_984_; size_t v_i_boxed_985_; lean_object* v_res_986_; 
v_sz_boxed_984_ = lean_unbox_usize(v_sz_981_);
lean_dec(v_sz_981_);
v_i_boxed_985_ = lean_unbox_usize(v_i_982_);
lean_dec(v_i_982_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_977_, v_00_u03b2_978_, v_00_u03c3_979_, v_f_980_, v_sz_boxed_984_, v_i_boxed_985_, v_bs_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_f_989_, lean_object* v_as_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_989_, v_as_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_f_994_, lean_object* v_as_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_992_, v_00_u03b2_993_, v_f_994_, v_as_995_);
lean_dec_ref(v_as_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_997_, lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_f_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1000_, v_x_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03c3_1004_, lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_f_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(v_00_u03c3_1004_, v_00_u03b1_1005_, v_00_u03b2_1006_, v_f_1007_, v_x_1008_, v_x_1009_);
lean_dec_ref(v_x_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_f_1013_, lean_object* v_as_1014_, lean_object* v_i_1015_, lean_object* v_acc_1016_, lean_object* v_hle_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_1013_, v_as_1014_, v_i_1015_, v_acc_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_00_u03b2_1020_, lean_object* v_f_1021_, lean_object* v_as_1022_, lean_object* v_i_1023_, lean_object* v_acc_1024_, lean_object* v_hle_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_1019_, v_00_u03b2_1020_, v_f_1021_, v_as_1022_, v_i_1023_, v_acc_1024_, v_hle_1025_);
lean_dec_ref(v_as_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(lean_object* v_00_u03b1_1027_, lean_object* v_00_u03b2_1028_, lean_object* v_00_u03c3_1029_, lean_object* v_f_1030_, lean_object* v_as_1031_, size_t v_i_1032_, size_t v_stop_1033_, lean_object* v_b_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_1030_, v_as_1031_, v_i_1032_, v_stop_1033_, v_b_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_00_u03c3_1038_, lean_object* v_f_1039_, lean_object* v_as_1040_, lean_object* v_i_1041_, lean_object* v_stop_1042_, lean_object* v_b_1043_){
_start:
{
size_t v_i_boxed_1044_; size_t v_stop_boxed_1045_; lean_object* v_res_1046_; 
v_i_boxed_1044_ = lean_unbox_usize(v_i_1041_);
lean_dec(v_i_1041_);
v_stop_boxed_1045_ = lean_unbox_usize(v_stop_1042_);
lean_dec(v_stop_1042_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(v_00_u03b1_1036_, v_00_u03b2_1037_, v_00_u03c3_1038_, v_f_1039_, v_as_1040_, v_i_boxed_1044_, v_stop_boxed_1045_, v_b_1043_);
lean_dec_ref(v_as_1040_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03c3_1047_, lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_f_1050_, lean_object* v_keys_1051_, lean_object* v_vals_1052_, lean_object* v_heq_1053_, lean_object* v_i_1054_, lean_object* v_acc_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_1050_, v_keys_1051_, v_vals_1052_, v_i_1054_, v_acc_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03c3_1057_, lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_f_1060_, lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_heq_1063_, lean_object* v_i_1064_, lean_object* v_acc_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(v_00_u03c3_1057_, v_00_u03b1_1058_, v_00_u03b2_1059_, v_f_1060_, v_keys_1061_, v_vals_1062_, v_heq_1063_, v_i_1064_, v_acc_1065_);
lean_dec_ref(v_vals_1062_);
lean_dec_ref(v_keys_1061_);
return v_res_1066_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_1067_, lean_object* v_opt_1068_){
_start:
{
lean_object* v_name_1069_; lean_object* v_defValue_1070_; lean_object* v_map_1071_; lean_object* v___x_1072_; 
v_name_1069_ = lean_ctor_get(v_opt_1068_, 0);
v_defValue_1070_ = lean_ctor_get(v_opt_1068_, 1);
v_map_1071_ = lean_ctor_get(v_opts_1067_, 0);
v___x_1072_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1071_, v_name_1069_);
if (lean_obj_tag(v___x_1072_) == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_unbox(v_defValue_1070_);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; 
v_val_1074_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v___x_1072_, 1);
if (lean_obj_tag(v_val_1074_) == 1)
{
uint8_t v_v_1075_; 
v_v_1075_ = lean_ctor_get_uint8(v_val_1074_, 0);
lean_dec_ref_known(v_val_1074_, 0);
return v_v_1075_;
}
else
{
uint8_t v___x_1076_; 
lean_dec(v_val_1074_);
v___x_1076_ = lean_unbox(v_defValue_1070_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_1077_, lean_object* v_opt_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_1077_, v_opt_1078_);
lean_dec_ref(v_opt_1078_);
lean_dec_ref(v_opts_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object* v_opts_1081_, lean_object* v_opt_1082_){
_start:
{
lean_object* v_name_1083_; lean_object* v_defValue_1084_; lean_object* v_map_1085_; lean_object* v___x_1086_; 
v_name_1083_ = lean_ctor_get(v_opt_1082_, 0);
v_defValue_1084_ = lean_ctor_get(v_opt_1082_, 1);
v_map_1085_ = lean_ctor_get(v_opts_1081_, 0);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1085_, v_name_1083_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_inc(v_defValue_1084_);
return v_defValue_1084_;
}
else
{
lean_object* v_val_1087_; 
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1086_, 1);
if (lean_obj_tag(v_val_1087_) == 3)
{
lean_object* v_v_1088_; 
v_v_1088_ = lean_ctor_get(v_val_1087_, 0);
lean_inc(v_v_1088_);
lean_dec_ref_known(v_val_1087_, 1);
return v_v_1088_;
}
else
{
lean_dec(v_val_1087_);
lean_inc(v_defValue_1084_);
return v_defValue_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object* v_opts_1089_, lean_object* v_opt_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_opts_1089_, v_opt_1090_);
lean_dec_ref(v_opt_1090_);
lean_dec_ref(v_opts_1089_);
return v_res_1091_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_unsigned_to_nat(32u);
v___x_1093_ = lean_mk_empty_array_with_capacity(v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
size_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1095_ = ((size_t)5ULL);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_unsigned_to_nat(32u);
v___x_1098_ = lean_mk_empty_array_with_capacity(v___x_1097_);
v___x_1099_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0);
v___x_1100_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v___x_1098_);
lean_ctor_set(v___x_1100_, 2, v___x_1096_);
lean_ctor_set(v___x_1100_, 3, v___x_1096_);
lean_ctor_set_usize(v___x_1100_, 4, v___x_1095_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_NameSet_empty;
v___x_1107_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_ctor_set(v___x_1108_, 2, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = l_Lean_firstFrontendMacroScope;
v___x_1111_ = lean_nat_add(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_1116_; uint64_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1117_ = 0ULL;
v___x_1118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set_uint64(v___x_1118_, sizeof(void*)*1, v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1120_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1121_ = 1;
v___x_1122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1119_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3, v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l_Lean_Options_empty;
v___x_1130_ = l_Lean_Core_getMaxHeartbeats(v___x_1129_);
return v___x_1130_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = l_Lean_diagnostics;
v___x_1132_ = l_Lean_Options_empty;
v___x_1133_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = l_Lean_maxRecDepth;
v___x_1135_ = l_Lean_Options_empty;
v___x_1136_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_a_1141_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_toCommandContextInfo_1148_; lean_object* v_env_1149_; lean_object* v_options_1150_; lean_object* v_currNamespace_1151_; lean_object* v_openDecls_1152_; lean_object* v_ngen_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___y_1167_; lean_object* v___y_1168_; lean_object* v_fileName_1169_; lean_object* v_fileMap_1170_; lean_object* v_currRecDepth_1171_; lean_object* v_ref_1172_; lean_object* v_currNamespace_1173_; lean_object* v_openDecls_1174_; lean_object* v_initHeartbeats_1175_; lean_object* v_maxHeartbeats_1176_; lean_object* v_quotContext_1177_; lean_object* v_currMacroScope_1178_; lean_object* v_cancelTk_x3f_1179_; uint8_t v_suppressElabErrors_1180_; lean_object* v_inheritedTraceOptions_1181_; lean_object* v___y_1182_; uint8_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_env_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___y_1275_; lean_object* v___y_1276_; uint8_t v___y_1306_; uint8_t v___x_1326_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_1146_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_1147_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_1148_ = lean_ctor_get(v_info_1137_, 0);
lean_inc_ref(v_toCommandContextInfo_1148_);
lean_dec_ref(v_info_1137_);
v_env_1149_ = lean_ctor_get(v_toCommandContextInfo_1148_, 0);
lean_inc_ref(v_env_1149_);
v_options_1150_ = lean_ctor_get(v_toCommandContextInfo_1148_, 4);
lean_inc_ref(v_options_1150_);
v_currNamespace_1151_ = lean_ctor_get(v_toCommandContextInfo_1148_, 5);
lean_inc(v_currNamespace_1151_);
v_openDecls_1152_ = lean_ctor_get(v_toCommandContextInfo_1148_, 6);
lean_inc(v_openDecls_1152_);
v_ngen_1153_ = lean_ctor_get(v_toCommandContextInfo_1148_, 7);
lean_inc_ref(v_ngen_1153_);
lean_dec_ref(v_toCommandContextInfo_1148_);
v___x_1154_ = l_Lean_firstFrontendMacroScope;
v___x_1155_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_1156_ = 0;
v_env_1157_ = l_Lean_Environment_setExporting(v_env_1149_, v___x_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7));
v___x_1160_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1161_ = 1;
v___x_1162_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_1164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1164_, 0, v_env_1157_);
lean_ctor_set(v___x_1164_, 1, v___x_1155_);
lean_ctor_set(v___x_1164_, 2, v_ngen_1153_);
lean_ctor_set(v___x_1164_, 3, v___x_1159_);
lean_ctor_set(v___x_1164_, 4, v___x_1160_);
lean_ctor_set(v___x_1164_, 5, v___x_1145_);
lean_ctor_set(v___x_1164_, 6, v___x_1146_);
lean_ctor_set(v___x_1164_, 7, v___x_1162_);
lean_ctor_set(v___x_1164_, 8, v___x_1163_);
v___x_1165_ = lean_st_mk_ref(v___x_1164_);
v___x_1260_ = l_Lean_inheritedTraceOptions;
v___x_1261_ = lean_st_ref_get(v___x_1260_);
v___x_1262_ = lean_st_ref_get(v___x_1165_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_1264_ = l_Lean_instInhabitedFileMap_default;
v___x_1265_ = l_Lean_Options_empty;
v___x_1266_ = lean_unsigned_to_nat(1000u);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1270_, 0, v___x_1263_);
lean_ctor_set(v___x_1270_, 1, v___x_1264_);
lean_ctor_set(v___x_1270_, 2, v___x_1265_);
lean_ctor_set(v___x_1270_, 3, v___x_1144_);
lean_ctor_set(v___x_1270_, 4, v___x_1266_);
lean_ctor_set(v___x_1270_, 5, v___x_1267_);
lean_ctor_set(v___x_1270_, 6, v_currNamespace_1151_);
lean_ctor_set(v___x_1270_, 7, v_openDecls_1152_);
lean_ctor_set(v___x_1270_, 8, v___x_1147_);
lean_ctor_set(v___x_1270_, 9, v___x_1268_);
lean_ctor_set(v___x_1270_, 10, v___x_1158_);
lean_ctor_set(v___x_1270_, 11, v___x_1154_);
lean_ctor_set(v___x_1270_, 12, v___x_1269_);
lean_ctor_set(v___x_1270_, 13, v___x_1261_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*14, v___x_1156_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*14 + 1, v___x_1156_);
v_env_1271_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_env_1271_);
lean_dec(v___x_1262_);
v___x_1272_ = l_Lean_diagnostics;
v___x_1273_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_1326_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1271_);
lean_dec_ref(v_env_1271_);
if (v___x_1326_ == 0)
{
if (v___x_1273_ == 0)
{
lean_inc(v___x_1165_);
v___y_1275_ = v___x_1270_;
v___y_1276_ = v___x_1165_;
goto v___jp_1274_;
}
else
{
v___y_1306_ = v___x_1326_;
goto v___jp_1305_;
}
}
else
{
v___y_1306_ = v___x_1273_;
goto v___jp_1305_;
}
v___jp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_mk_io_user_error(v_a_1141_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
v___jp_1166_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_1150_, v___y_1168_);
v___x_1184_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1184_, 0, v_fileName_1169_);
lean_ctor_set(v___x_1184_, 1, v_fileMap_1170_);
lean_ctor_set(v___x_1184_, 2, v_options_1150_);
lean_ctor_set(v___x_1184_, 3, v_currRecDepth_1171_);
lean_ctor_set(v___x_1184_, 4, v___x_1183_);
lean_ctor_set(v___x_1184_, 5, v_ref_1172_);
lean_ctor_set(v___x_1184_, 6, v_currNamespace_1173_);
lean_ctor_set(v___x_1184_, 7, v_openDecls_1174_);
lean_ctor_set(v___x_1184_, 8, v_initHeartbeats_1175_);
lean_ctor_set(v___x_1184_, 9, v_maxHeartbeats_1176_);
lean_ctor_set(v___x_1184_, 10, v_quotContext_1177_);
lean_ctor_set(v___x_1184_, 11, v_currMacroScope_1178_);
lean_ctor_set(v___x_1184_, 12, v_cancelTk_x3f_1179_);
lean_ctor_set(v___x_1184_, 13, v_inheritedTraceOptions_1181_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*14, v___y_1167_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*14 + 1, v_suppressElabErrors_1180_);
v___x_1185_ = lean_apply_3(v_x_1138_, v___x_1184_, v___y_1182_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_st_ref_get(v___x_1165_);
lean_dec(v___x_1165_);
lean_dec(v___x_1190_);
if (v_isShared_1189_ == 0)
{
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1186_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v___x_1165_);
v_a_1195_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1197_ = v___x_1185_;
v_isShared_1198_ = v_isSharedCheck_1216_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1185_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1216_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
if (lean_obj_tag(v_a_1195_) == 0)
{
lean_object* v_msg_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_msg_1199_ = lean_ctor_get(v_a_1195_, 1);
lean_inc_ref(v_msg_1199_);
lean_dec_ref_known(v_a_1195_, 2);
v___x_1200_ = l_Lean_MessageData_toString(v_msg_1199_);
v___x_1201_ = lean_mk_io_user_error(v___x_1200_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1201_);
v___x_1203_ = v___x_1197_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v_id_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1197_);
v_id_1205_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_id_1205_);
lean_dec_ref_known(v_a_1195_, 2);
v___x_1206_ = l_Lean_InternalExceptionId_getName(v_id_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v_id_1205_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_1209_ = l_Lean_Name_toString(v_a_1207_, v___x_1161_);
v___x_1210_ = lean_string_append(v___x_1208_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v_a_1141_ = v___x_1210_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_1212_ = l_Nat_reprFast(v_id_1205_);
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_1215_ = lean_string_append(v___x_1213_, v___x_1214_);
v_a_1141_ = v___x_1215_;
goto v___jp_1140_;
}
}
}
}
}
v___jp_1217_:
{
lean_object* v_fileName_1222_; lean_object* v_fileMap_1223_; lean_object* v_currRecDepth_1224_; lean_object* v_ref_1225_; lean_object* v_currNamespace_1226_; lean_object* v_openDecls_1227_; lean_object* v_initHeartbeats_1228_; lean_object* v_maxHeartbeats_1229_; lean_object* v_quotContext_1230_; lean_object* v_currMacroScope_1231_; lean_object* v_cancelTk_x3f_1232_; uint8_t v_suppressElabErrors_1233_; lean_object* v_inheritedTraceOptions_1234_; 
v_fileName_1222_ = lean_ctor_get(v___y_1220_, 0);
lean_inc_ref(v_fileName_1222_);
v_fileMap_1223_ = lean_ctor_get(v___y_1220_, 1);
lean_inc_ref(v_fileMap_1223_);
v_currRecDepth_1224_ = lean_ctor_get(v___y_1220_, 3);
lean_inc(v_currRecDepth_1224_);
v_ref_1225_ = lean_ctor_get(v___y_1220_, 5);
lean_inc(v_ref_1225_);
v_currNamespace_1226_ = lean_ctor_get(v___y_1220_, 6);
lean_inc(v_currNamespace_1226_);
v_openDecls_1227_ = lean_ctor_get(v___y_1220_, 7);
lean_inc(v_openDecls_1227_);
v_initHeartbeats_1228_ = lean_ctor_get(v___y_1220_, 8);
lean_inc(v_initHeartbeats_1228_);
v_maxHeartbeats_1229_ = lean_ctor_get(v___y_1220_, 9);
lean_inc(v_maxHeartbeats_1229_);
v_quotContext_1230_ = lean_ctor_get(v___y_1220_, 10);
lean_inc(v_quotContext_1230_);
v_currMacroScope_1231_ = lean_ctor_get(v___y_1220_, 11);
lean_inc(v_currMacroScope_1231_);
v_cancelTk_x3f_1232_ = lean_ctor_get(v___y_1220_, 12);
lean_inc(v_cancelTk_x3f_1232_);
v_suppressElabErrors_1233_ = lean_ctor_get_uint8(v___y_1220_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1234_ = lean_ctor_get(v___y_1220_, 13);
lean_inc_ref(v_inheritedTraceOptions_1234_);
lean_dec_ref(v___y_1220_);
v___y_1167_ = v___y_1218_;
v___y_1168_ = v___y_1219_;
v_fileName_1169_ = v_fileName_1222_;
v_fileMap_1170_ = v_fileMap_1223_;
v_currRecDepth_1171_ = v_currRecDepth_1224_;
v_ref_1172_ = v_ref_1225_;
v_currNamespace_1173_ = v_currNamespace_1226_;
v_openDecls_1174_ = v_openDecls_1227_;
v_initHeartbeats_1175_ = v_initHeartbeats_1228_;
v_maxHeartbeats_1176_ = v_maxHeartbeats_1229_;
v_quotContext_1177_ = v_quotContext_1230_;
v_currMacroScope_1178_ = v_currMacroScope_1231_;
v_cancelTk_x3f_1179_ = v_cancelTk_x3f_1232_;
v_suppressElabErrors_1180_ = v_suppressElabErrors_1233_;
v_inheritedTraceOptions_1181_ = v_inheritedTraceOptions_1234_;
v___y_1182_ = v___y_1221_;
goto v___jp_1166_;
}
v___jp_1235_:
{
if (v___y_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v_env_1242_; lean_object* v_nextMacroScope_1243_; lean_object* v_ngen_1244_; lean_object* v_auxDeclNGen_1245_; lean_object* v_traceState_1246_; lean_object* v_messages_1247_; lean_object* v_infoState_1248_; lean_object* v_snapshotTasks_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
v___x_1241_ = lean_st_ref_take(v___y_1238_);
v_env_1242_ = lean_ctor_get(v___x_1241_, 0);
v_nextMacroScope_1243_ = lean_ctor_get(v___x_1241_, 1);
v_ngen_1244_ = lean_ctor_get(v___x_1241_, 2);
v_auxDeclNGen_1245_ = lean_ctor_get(v___x_1241_, 3);
v_traceState_1246_ = lean_ctor_get(v___x_1241_, 4);
v_messages_1247_ = lean_ctor_get(v___x_1241_, 6);
v_infoState_1248_ = lean_ctor_get(v___x_1241_, 7);
v_snapshotTasks_1249_ = lean_ctor_get(v___x_1241_, 8);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1241_, 5);
lean_dec(v_unused_1259_);
v___x_1251_ = v___x_1241_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snapshotTasks_1249_);
lean_inc(v_infoState_1248_);
lean_inc(v_messages_1247_);
lean_inc(v_traceState_1246_);
lean_inc(v_auxDeclNGen_1245_);
lean_inc(v_ngen_1244_);
lean_inc(v_nextMacroScope_1243_);
lean_inc(v_env_1242_);
lean_dec(v___x_1241_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = l_Lean_Kernel_enableDiag(v_env_1242_, v___y_1237_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 5, v___x_1145_);
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1244_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1246_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_infoState_1248_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1249_);
v___x_1255_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_st_ref_set(v___y_1238_, v___x_1255_);
v___y_1218_ = v___y_1237_;
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1239_;
v___y_1221_ = v___y_1238_;
goto v___jp_1217_;
}
}
}
else
{
v___y_1218_ = v___y_1237_;
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1239_;
v___y_1221_ = v___y_1238_;
goto v___jp_1217_;
}
}
v___jp_1274_:
{
lean_object* v___x_1277_; lean_object* v_fileName_1278_; lean_object* v_fileMap_1279_; lean_object* v_currRecDepth_1280_; lean_object* v_ref_1281_; lean_object* v_currNamespace_1282_; lean_object* v_openDecls_1283_; lean_object* v_initHeartbeats_1284_; lean_object* v_maxHeartbeats_1285_; lean_object* v_quotContext_1286_; lean_object* v_currMacroScope_1287_; lean_object* v_cancelTk_x3f_1288_; uint8_t v_suppressElabErrors_1289_; lean_object* v_inheritedTraceOptions_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1302_; 
v___x_1277_ = lean_st_ref_get(v___y_1276_);
v_fileName_1278_ = lean_ctor_get(v___y_1275_, 0);
v_fileMap_1279_ = lean_ctor_get(v___y_1275_, 1);
v_currRecDepth_1280_ = lean_ctor_get(v___y_1275_, 3);
v_ref_1281_ = lean_ctor_get(v___y_1275_, 5);
v_currNamespace_1282_ = lean_ctor_get(v___y_1275_, 6);
v_openDecls_1283_ = lean_ctor_get(v___y_1275_, 7);
v_initHeartbeats_1284_ = lean_ctor_get(v___y_1275_, 8);
v_maxHeartbeats_1285_ = lean_ctor_get(v___y_1275_, 9);
v_quotContext_1286_ = lean_ctor_get(v___y_1275_, 10);
v_currMacroScope_1287_ = lean_ctor_get(v___y_1275_, 11);
v_cancelTk_x3f_1288_ = lean_ctor_get(v___y_1275_, 12);
v_suppressElabErrors_1289_ = lean_ctor_get_uint8(v___y_1275_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1290_ = lean_ctor_get(v___y_1275_, 13);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___y_1275_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; lean_object* v_unused_1304_; 
v_unused_1303_ = lean_ctor_get(v___y_1275_, 4);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v___y_1275_, 2);
lean_dec(v_unused_1304_);
v___x_1292_ = v___y_1275_;
v_isShared_1293_ = v_isSharedCheck_1302_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_inheritedTraceOptions_1290_);
lean_inc(v_cancelTk_x3f_1288_);
lean_inc(v_currMacroScope_1287_);
lean_inc(v_quotContext_1286_);
lean_inc(v_maxHeartbeats_1285_);
lean_inc(v_initHeartbeats_1284_);
lean_inc(v_openDecls_1283_);
lean_inc(v_currNamespace_1282_);
lean_inc(v_ref_1281_);
lean_inc(v_currRecDepth_1280_);
lean_inc(v_fileMap_1279_);
lean_inc(v_fileName_1278_);
lean_dec(v___y_1275_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1302_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_env_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v_env_1294_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_env_1294_);
lean_dec(v___x_1277_);
v___x_1295_ = l_Lean_maxRecDepth;
v___x_1296_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_1290_);
lean_inc(v_cancelTk_x3f_1288_);
lean_inc(v_currMacroScope_1287_);
lean_inc(v_quotContext_1286_);
lean_inc(v_maxHeartbeats_1285_);
lean_inc(v_initHeartbeats_1284_);
lean_inc(v_openDecls_1283_);
lean_inc(v_currNamespace_1282_);
lean_inc(v_ref_1281_);
lean_inc(v_currRecDepth_1280_);
lean_inc_ref(v_fileMap_1279_);
lean_inc_ref(v_fileName_1278_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1296_);
lean_ctor_set(v___x_1292_, 2, v___x_1265_);
v___x_1298_ = v___x_1292_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_fileName_1278_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_fileMap_1279_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v_currRecDepth_1280_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1301_, 5, v_ref_1281_);
lean_ctor_set(v_reuseFailAlloc_1301_, 6, v_currNamespace_1282_);
lean_ctor_set(v_reuseFailAlloc_1301_, 7, v_openDecls_1283_);
lean_ctor_set(v_reuseFailAlloc_1301_, 8, v_initHeartbeats_1284_);
lean_ctor_set(v_reuseFailAlloc_1301_, 9, v_maxHeartbeats_1285_);
lean_ctor_set(v_reuseFailAlloc_1301_, 10, v_quotContext_1286_);
lean_ctor_set(v_reuseFailAlloc_1301_, 11, v_currMacroScope_1287_);
lean_ctor_set(v_reuseFailAlloc_1301_, 12, v_cancelTk_x3f_1288_);
lean_ctor_set(v_reuseFailAlloc_1301_, 13, v_inheritedTraceOptions_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*14 + 1, v_suppressElabErrors_1289_);
v___x_1298_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
uint8_t v___x_1299_; uint8_t v___x_1300_; 
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*14, v___x_1273_);
v___x_1299_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_1150_, v___x_1272_);
v___x_1300_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1294_);
lean_dec_ref(v_env_1294_);
if (v___x_1300_ == 0)
{
if (v___x_1299_ == 0)
{
lean_dec_ref(v___x_1298_);
v___y_1167_ = v___x_1299_;
v___y_1168_ = v___x_1295_;
v_fileName_1169_ = v_fileName_1278_;
v_fileMap_1170_ = v_fileMap_1279_;
v_currRecDepth_1171_ = v_currRecDepth_1280_;
v_ref_1172_ = v_ref_1281_;
v_currNamespace_1173_ = v_currNamespace_1282_;
v_openDecls_1174_ = v_openDecls_1283_;
v_initHeartbeats_1175_ = v_initHeartbeats_1284_;
v_maxHeartbeats_1176_ = v_maxHeartbeats_1285_;
v_quotContext_1177_ = v_quotContext_1286_;
v_currMacroScope_1178_ = v_currMacroScope_1287_;
v_cancelTk_x3f_1179_ = v_cancelTk_x3f_1288_;
v_suppressElabErrors_1180_ = v_suppressElabErrors_1289_;
v_inheritedTraceOptions_1181_ = v_inheritedTraceOptions_1290_;
v___y_1182_ = v___y_1276_;
goto v___jp_1166_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1290_);
lean_dec(v_cancelTk_x3f_1288_);
lean_dec(v_currMacroScope_1287_);
lean_dec(v_quotContext_1286_);
lean_dec(v_maxHeartbeats_1285_);
lean_dec(v_initHeartbeats_1284_);
lean_dec(v_openDecls_1283_);
lean_dec(v_currNamespace_1282_);
lean_dec(v_ref_1281_);
lean_dec(v_currRecDepth_1280_);
lean_dec_ref(v_fileMap_1279_);
lean_dec_ref(v_fileName_1278_);
v___y_1236_ = v___x_1295_;
v___y_1237_ = v___x_1299_;
v___y_1238_ = v___y_1276_;
v___y_1239_ = v___x_1298_;
v___y_1240_ = v___x_1300_;
goto v___jp_1235_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1290_);
lean_dec(v_cancelTk_x3f_1288_);
lean_dec(v_currMacroScope_1287_);
lean_dec(v_quotContext_1286_);
lean_dec(v_maxHeartbeats_1285_);
lean_dec(v_initHeartbeats_1284_);
lean_dec(v_openDecls_1283_);
lean_dec(v_currNamespace_1282_);
lean_dec(v_ref_1281_);
lean_dec(v_currRecDepth_1280_);
lean_dec_ref(v_fileMap_1279_);
lean_dec_ref(v_fileName_1278_);
v___y_1236_ = v___x_1295_;
v___y_1237_ = v___x_1299_;
v___y_1238_ = v___y_1276_;
v___y_1239_ = v___x_1298_;
v___y_1240_ = v___x_1299_;
goto v___jp_1235_;
}
}
}
}
v___jp_1305_:
{
if (v___y_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v_env_1308_; lean_object* v_nextMacroScope_1309_; lean_object* v_ngen_1310_; lean_object* v_auxDeclNGen_1311_; lean_object* v_traceState_1312_; lean_object* v_messages_1313_; lean_object* v_infoState_1314_; lean_object* v_snapshotTasks_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1324_; 
v___x_1307_ = lean_st_ref_take(v___x_1165_);
v_env_1308_ = lean_ctor_get(v___x_1307_, 0);
v_nextMacroScope_1309_ = lean_ctor_get(v___x_1307_, 1);
v_ngen_1310_ = lean_ctor_get(v___x_1307_, 2);
v_auxDeclNGen_1311_ = lean_ctor_get(v___x_1307_, 3);
v_traceState_1312_ = lean_ctor_get(v___x_1307_, 4);
v_messages_1313_ = lean_ctor_get(v___x_1307_, 6);
v_infoState_1314_ = lean_ctor_get(v___x_1307_, 7);
v_snapshotTasks_1315_ = lean_ctor_get(v___x_1307_, 8);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1307_, 5);
lean_dec(v_unused_1325_);
v___x_1317_ = v___x_1307_;
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snapshotTasks_1315_);
lean_inc(v_infoState_1314_);
lean_inc(v_messages_1313_);
lean_inc(v_traceState_1312_);
lean_inc(v_auxDeclNGen_1311_);
lean_inc(v_ngen_1310_);
lean_inc(v_nextMacroScope_1309_);
lean_inc(v_env_1308_);
lean_dec(v___x_1307_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = l_Lean_Kernel_enableDiag(v_env_1308_, v___x_1273_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 5, v___x_1145_);
lean_ctor_set(v___x_1317_, 0, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_nextMacroScope_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_ngen_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_auxDeclNGen_1311_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_traceState_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_messages_1313_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v_infoState_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v_snapshotTasks_1315_);
v___x_1321_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_st_ref_set(v___x_1165_, v___x_1321_);
lean_inc(v___x_1165_);
v___y_1275_ = v___x_1270_;
v___y_1276_ = v___x_1165_;
goto v___jp_1274_;
}
}
}
else
{
lean_inc(v___x_1165_);
v___y_1275_ = v___x_1270_;
v___y_1276_ = v___x_1165_;
goto v___jp_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_1327_, lean_object* v_x_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1327_, v_x_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_1331_, lean_object* v_info_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1332_, v_x_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_info_1337_, lean_object* v_x_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_1336_, v_info_1337_, v_x_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_1341_, lean_object* v_x_1342_, lean_object* v___x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_st_mk_ref(v___x_1341_);
lean_inc(v___x_1347_);
v___x_1348_ = lean_apply_5(v_x_1342_, v___x_1343_, v___x_1347_, v___y_1344_, v___y_1345_, lean_box(0));
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1358_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = lean_st_ref_get(v___x_1347_);
lean_dec(v___x_1347_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_a_1349_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
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
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___x_1347_);
v_a_1359_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1348_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1348_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_1367_, lean_object* v_x_1368_, lean_object* v___x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_1367_, v_x_1368_, v___x_1369_, v___y_1370_, v___y_1371_);
return v_res_1373_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1380_; uint64_t v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1381_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1380_);
return v___x_1381_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1384_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set_uint64(v___x_1384_, sizeof(void*)*1, v___x_1382_);
return v___x_1384_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
lean_ctor_set(v___x_1391_, 3, v___x_1390_);
lean_ctor_set(v___x_1391_, 4, v___x_1390_);
lean_ctor_set(v___x_1391_, 5, v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(32u);
v___x_1393_ = lean_mk_empty_array_with_capacity(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1395_ = ((size_t)5ULL);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_unsigned_to_nat(32u);
v___x_1398_ = lean_mk_empty_array_with_capacity(v___x_1397_);
v___x_1399_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_1400_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
lean_ctor_set(v___x_1400_, 2, v___x_1396_);
lean_ctor_set(v___x_1400_, 3, v___x_1396_);
lean_ctor_set_usize(v___x_1400_, 4, v___x_1395_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
lean_ctor_set(v___x_1402_, 3, v___x_1401_);
lean_ctor_set(v___x_1402_, 4, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_1403_, lean_object* v_lctx_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_toCommandContextInfo_1415_; lean_object* v_mctx_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; 
v___x_1407_ = lean_box(1);
v___x_1408_ = 0;
v___x_1409_ = 1;
v___x_1410_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1414_, 0, v___x_1410_);
lean_ctor_set(v___x_1414_, 1, v___x_1407_);
lean_ctor_set(v___x_1414_, 2, v_lctx_1404_);
lean_ctor_set(v___x_1414_, 3, v___x_1412_);
lean_ctor_set(v___x_1414_, 4, v___x_1413_);
lean_ctor_set(v___x_1414_, 5, v___x_1411_);
lean_ctor_set(v___x_1414_, 6, v___x_1413_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*7, v___x_1408_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*7 + 1, v___x_1408_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*7 + 2, v___x_1408_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*7 + 3, v___x_1409_);
v_toCommandContextInfo_1415_ = lean_ctor_get(v_info_1403_, 0);
v_mctx_1416_ = lean_ctor_get(v_toCommandContextInfo_1415_, 3);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_1418_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_1419_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_1416_);
v___x_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1420_, 0, v_mctx_1416_);
lean_ctor_set(v___x_1420_, 1, v___x_1417_);
lean_ctor_set(v___x_1420_, 2, v___x_1407_);
lean_ctor_set(v___x_1420_, 3, v___x_1418_);
lean_ctor_set(v___x_1420_, 4, v___x_1419_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1421_, 0, v___x_1420_);
lean_closure_set(v___f_1421_, 1, v_x_1405_);
lean_closure_set(v___f_1421_, 2, v___x_1414_);
v___x_1422_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1403_, v___f_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_fst_1427_; lean_object* v___x_1429_; 
v_fst_1427_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_fst_1427_);
lean_dec(v_a_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_fst_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_fst_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1422_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1422_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_1440_, lean_object* v_lctx_1441_, lean_object* v_x_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1440_, v_lctx_1441_, v_x_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_1445_, lean_object* v_info_1446_, lean_object* v_lctx_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1446_, v_lctx_1447_, v_x_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_info_1452_, lean_object* v_lctx_1453_, lean_object* v_x_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_1451_, v_info_1452_, v_lctx_1453_, v_x_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_1457_, lean_object* v_lctx_1458_){
_start:
{
lean_object* v_toCommandContextInfo_1459_; lean_object* v_env_1460_; lean_object* v_mctx_1461_; lean_object* v_options_1462_; lean_object* v_currNamespace_1463_; lean_object* v_openDecls_1464_; lean_object* v___x_1465_; 
v_toCommandContextInfo_1459_ = lean_ctor_get(v_info_1457_, 0);
v_env_1460_ = lean_ctor_get(v_toCommandContextInfo_1459_, 0);
v_mctx_1461_ = lean_ctor_get(v_toCommandContextInfo_1459_, 3);
v_options_1462_ = lean_ctor_get(v_toCommandContextInfo_1459_, 4);
v_currNamespace_1463_ = lean_ctor_get(v_toCommandContextInfo_1459_, 5);
v_openDecls_1464_ = lean_ctor_get(v_toCommandContextInfo_1459_, 6);
lean_inc(v_openDecls_1464_);
lean_inc(v_currNamespace_1463_);
lean_inc_ref(v_options_1462_);
lean_inc_ref(v_mctx_1461_);
lean_inc_ref(v_env_1460_);
v___x_1465_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1465_, 0, v_env_1460_);
lean_ctor_set(v___x_1465_, 1, v_mctx_1461_);
lean_ctor_set(v___x_1465_, 2, v_lctx_1458_);
lean_ctor_set(v___x_1465_, 3, v_options_1462_);
lean_ctor_set(v___x_1465_, 4, v_currNamespace_1463_);
lean_ctor_set(v___x_1465_, 5, v_openDecls_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_1466_, lean_object* v_lctx_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1466_, v_lctx_1467_);
lean_dec_ref(v_info_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_1469_, lean_object* v_lctx_1470_, lean_object* v_stx_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1469_, v_lctx_1470_);
v___x_1474_ = l_Lean_ppTerm(v___x_1473_, v_stx_1471_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_1476_, lean_object* v_lctx_1477_, lean_object* v_stx_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_1476_, v_lctx_1477_, v_stx_1478_);
lean_dec_ref(v_info_1476_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_1496_, lean_object* v_pos_1497_, lean_object* v_info_1498_){
_start:
{
lean_object* v_toCommandContextInfo_1499_; lean_object* v_fileMap_1500_; lean_object* v___x_1501_; lean_object* v_line_1502_; lean_object* v_column_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1526_; 
v_toCommandContextInfo_1499_ = lean_ctor_get(v_ctx_1496_, 0);
lean_inc_ref(v_toCommandContextInfo_1499_);
lean_dec_ref(v_ctx_1496_);
v_fileMap_1500_ = lean_ctor_get(v_toCommandContextInfo_1499_, 2);
lean_inc_ref(v_fileMap_1500_);
lean_dec_ref(v_toCommandContextInfo_1499_);
v___x_1501_ = l_Lean_FileMap_toPosition(v_fileMap_1500_, v_pos_1497_);
v_line_1502_ = lean_ctor_get(v___x_1501_, 0);
v_column_1503_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1505_ = v___x_1501_;
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_column_1503_);
lean_inc(v_line_1502_);
lean_dec(v___x_1501_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1508_ = l_Nat_reprFast(v_line_1502_);
v___x_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 5);
lean_ctor_set(v___x_1505_, 1, v___x_1509_);
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1511_ = v___x_1505_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_pos_1518_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_1513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Nat_reprFast(v_column_1503_);
v___x_1515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1513_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_1518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_1518_, 0, v___x_1516_);
lean_ctor_set(v_pos_1518_, 1, v___x_1517_);
switch(lean_obj_tag(v_info_1498_))
{
case 0:
{
return v_pos_1518_;
}
case 1:
{
uint8_t v_canonical_1522_; 
v_canonical_1522_ = lean_ctor_get_uint8(v_info_1498_, sizeof(void*)*2);
if (v_canonical_1522_ == 1)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_pos_1518_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
return v___x_1524_;
}
else
{
goto v___jp_1519_;
}
}
default: 
{
goto v___jp_1519_;
}
}
v___jp_1519_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_1521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_pos_1518_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_1527_, lean_object* v_pos_1528_, lean_object* v_info_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1527_, v_pos_1528_, v_info_1529_);
lean_dec(v_info_1529_);
lean_dec(v_pos_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_1534_, lean_object* v_stx_1535_){
_start:
{
lean_object* v___y_1537_; lean_object* v___y_1538_; uint8_t v___x_1546_; lean_object* v___y_1548_; lean_object* v___x_1551_; 
v___x_1546_ = 0;
v___x_1551_ = l_Lean_Syntax_getPos_x3f(v_stx_1535_, v___x_1546_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___y_1548_ = v___x_1552_;
goto v___jp_1547_;
}
else
{
lean_object* v_val_1553_; 
v_val_1553_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1551_, 1);
v___y_1548_ = v_val_1553_;
goto v___jp_1547_;
}
v___jp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1539_ = l_Lean_Syntax_getHeadInfo(v_stx_1535_);
lean_inc_ref(v_ctx_1534_);
v___x_1540_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1534_, v___y_1537_, v___x_1539_);
lean_dec(v___x_1539_);
lean_dec(v___y_1537_);
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = l_Lean_Syntax_getTailInfo(v_stx_1535_);
v___x_1544_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1534_, v___y_1538_, v___x_1543_);
lean_dec(v___x_1543_);
lean_dec(v___y_1538_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
v___jp_1547_:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1535_, v___x_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_inc(v___y_1548_);
v___y_1537_ = v___y_1548_;
v___y_1538_ = v___y_1548_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1550_; 
v_val_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___y_1537_ = v___y_1548_;
v___y_1538_ = v_val_1550_;
goto v___jp_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_1554_, lean_object* v_stx_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1554_, v_stx_1555_);
lean_dec(v_stx_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_1560_, lean_object* v_info_1561_){
_start:
{
lean_object* v_elaborator_1562_; lean_object* v_stx_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1578_; 
v_elaborator_1562_ = lean_ctor_get(v_info_1561_, 0);
v_stx_1563_ = lean_ctor_get(v_info_1561_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_info_1561_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1565_ = v_info_1561_;
v_isShared_1566_ = v_isSharedCheck_1578_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_stx_1563_);
lean_inc(v_elaborator_1562_);
lean_dec(v_info_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1578_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_Name_isAnonymous(v_elaborator_1562_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1560_, v_stx_1563_);
lean_dec(v_stx_1563_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 5);
lean_ctor_set(v___x_1565_, 1, v___x_1569_);
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1571_ = v___x_1565_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = 1;
v___x_1573_ = l_Lean_Name_toString(v_elaborator_1562_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1571_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
return v___x_1575_;
}
}
else
{
lean_object* v___x_1577_; 
lean_del_object(v___x_1565_);
lean_dec(v_elaborator_1562_);
v___x_1577_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1560_, v_stx_1563_);
lean_dec(v_stx_1563_);
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_1579_, lean_object* v_ctx_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v_lctx_1583_; lean_object* v___x_1584_; 
v_lctx_1583_ = lean_ctor_get(v_info_1579_, 1);
lean_inc_ref(v_lctx_1583_);
lean_dec_ref(v_info_1579_);
v___x_1584_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1580_, v_lctx_1583_, v_x_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_1585_, lean_object* v_ctx_1586_, lean_object* v_x_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1585_, v_ctx_1586_, v_x_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_1590_, lean_object* v_info_1591_, lean_object* v_ctx_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1591_, v_ctx_1592_, v_x_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_info_1597_, lean_object* v_ctx_1598_, lean_object* v_x_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_1596_, v_info_1597_, v_ctx_1598_, v_x_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_1616_, lean_object* v_toElabInfo_1617_, lean_object* v_expr_1618_, uint8_t v_isBinder_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v_a_1640_; lean_object* v___y_1650_; uint8_t v___y_1651_; lean_object* v___y_1654_; lean_object* v_a_1655_; lean_object* v___x_1658_; 
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
lean_inc(v___y_1621_);
lean_inc_ref(v___y_1620_);
lean_inc_ref(v_expr_1618_);
v___x_1658_ = lean_infer_type(v_expr_1618_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l_Lean_Meta_ppExpr(v_a_1659_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v_a_1640_ = v_a_1661_;
goto v___jp_1639_;
}
else
{
lean_object* v_a_1662_; 
v_a_1662_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1662_);
v___y_1654_ = v___x_1660_;
v_a_1655_ = v_a_1662_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1658_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1658_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
lean_inc(v_a_1663_);
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v___y_1654_ = v___x_1668_;
v_a_1655_ = v_a_1663_;
goto v___jp_1653_;
}
}
}
v___jp_1625_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc_ref(v___y_1628_);
v___x_1629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1628_);
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___y_1626_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___y_1627_);
v___x_1634_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1616_, v_toElabInfo_1617_);
v___x_1637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
v___jp_1639_:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_ppExpr(v_expr_1618_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1642_);
v___x_1645_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
if (v_isBinder_1619_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_1626_ = v___x_1646_;
v___y_1627_ = v_a_1640_;
v___y_1628_ = v___x_1647_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_1626_ = v___x_1646_;
v___y_1627_ = v_a_1640_;
v___y_1628_ = v___x_1648_;
goto v___jp_1625_;
}
}
else
{
lean_dec(v_a_1640_);
lean_dec_ref(v_toElabInfo_1617_);
lean_dec_ref(v_ctx_1616_);
return v___x_1641_;
}
}
v___jp_1649_:
{
if (v___y_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec_ref(v___y_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_1640_ = v___x_1652_;
goto v___jp_1639_;
}
else
{
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_expr_1618_);
lean_dec_ref(v_toElabInfo_1617_);
lean_dec_ref(v_ctx_1616_);
return v___y_1650_;
}
}
v___jp_1653_:
{
uint8_t v___x_1656_; 
v___x_1656_ = l_Lean_Exception_isInterrupt(v_a_1655_);
if (v___x_1656_ == 0)
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Lean_Exception_isRuntime(v_a_1655_);
v___y_1650_ = v___y_1654_;
v___y_1651_ = v___x_1657_;
goto v___jp_1649_;
}
else
{
lean_dec_ref(v_a_1655_);
v___y_1650_ = v___y_1654_;
v___y_1651_ = v___x_1656_;
goto v___jp_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_1671_, lean_object* v_toElabInfo_1672_, lean_object* v_expr_1673_, lean_object* v_isBinder_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v_isBinder_boxed_1680_; lean_object* v_res_1681_; 
v_isBinder_boxed_1680_ = lean_unbox(v_isBinder_1674_);
v_res_1681_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_1671_, v_toElabInfo_1672_, v_expr_1673_, v_isBinder_boxed_1680_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_1682_, lean_object* v_info_1683_){
_start:
{
lean_object* v_toElabInfo_1685_; lean_object* v_expr_1686_; uint8_t v_isBinder_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; 
v_toElabInfo_1685_ = lean_ctor_get(v_info_1683_, 0);
v_expr_1686_ = lean_ctor_get(v_info_1683_, 3);
v_isBinder_1687_ = lean_ctor_get_uint8(v_info_1683_, sizeof(void*)*4);
v___x_1688_ = lean_box(v_isBinder_1687_);
lean_inc_ref(v_expr_1686_);
lean_inc_ref(v_toElabInfo_1685_);
lean_inc_ref(v_ctx_1682_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1689_, 0, v_ctx_1682_);
lean_closure_set(v___f_1689_, 1, v_toElabInfo_1685_);
lean_closure_set(v___f_1689_, 2, v_expr_1686_);
lean_closure_set(v___f_1689_, 3, v___x_1688_);
v___x_1690_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1683_, v_ctx_1682_, v___f_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_1691_, lean_object* v_info_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_TermInfo_format(v_ctx_1691_, v_info_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_1698_, lean_object* v_info_1699_){
_start:
{
lean_object* v_toElabInfo_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_toElabInfo_1700_ = lean_ctor_get(v_info_1699_, 0);
lean_inc_ref(v_toElabInfo_1700_);
lean_dec_ref(v_info_1699_);
v___x_1701_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_1702_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1698_, v_toElabInfo_1700_);
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1711_;
}
else
{
lean_object* v_val_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1722_; 
v_val_1712_ = lean_ctor_get(v_x_1710_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1714_ = v_x_1710_;
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_val_1712_);
lean_dec(v_x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1716_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1717_ = lean_expr_dbg_to_string(v_val_1712_);
lean_dec(v_val_1712_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 3);
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1716_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_1729_, lean_object* v_lctx_1730_, lean_object* v_stx_1731_, lean_object* v_expectedType_x3f_1732_, lean_object* v_info_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1758_; 
v___x_1739_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1729_, v_lctx_1730_, v_stx_1731_);
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1740_);
v___x_1746_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1732_);
v___x_1749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_Elab_CompletionInfo_stx(v_info_1733_);
v___x_1753_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1729_, v___x_1752_);
lean_dec(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1751_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1754_);
v___x_1756_ = v___x_1742_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_1759_, lean_object* v_lctx_1760_, lean_object* v_stx_1761_, lean_object* v_expectedType_x3f_1762_, lean_object* v_info_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_1759_, v_lctx_1760_, v_stx_1761_, v_expectedType_x3f_1762_, v_info_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_info_1763_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_1776_, lean_object* v_info_1777_){
_start:
{
switch(lean_obj_tag(v_info_1777_))
{
case 0:
{
lean_object* v_termInfo_1779_; lean_object* v_expectedType_x3f_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1801_; 
v_termInfo_1779_ = lean_ctor_get(v_info_1777_, 0);
v_expectedType_x3f_1780_ = lean_ctor_get(v_info_1777_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_info_1777_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1782_ = v_info_1777_;
v_isShared_1783_ = v_isSharedCheck_1801_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_expectedType_x3f_1780_);
lean_inc(v_termInfo_1779_);
lean_dec(v_info_1777_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1801_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Elab_TermInfo_format(v_ctx_1776_, v_termInfo_1779_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1800_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1800_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1800_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 5);
lean_ctor_set(v___x_1782_, 1, v_a_1785_);
lean_ctor_set(v___x_1782_, 0, v___x_1789_);
v___x_1791_ = v___x_1782_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_a_1785_);
v___x_1791_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1792_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1780_);
v___x_1795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1795_);
v___x_1797_ = v___x_1787_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_del_object(v___x_1782_);
lean_dec(v_expectedType_x3f_1780_);
return v___x_1784_;
}
}
}
case 1:
{
lean_object* v_stx_1802_; lean_object* v_lctx_1803_; lean_object* v_expectedType_x3f_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; 
v_stx_1802_ = lean_ctor_get(v_info_1777_, 0);
lean_inc(v_stx_1802_);
v_lctx_1803_ = lean_ctor_get(v_info_1777_, 2);
lean_inc_ref_n(v_lctx_1803_, 2);
v_expectedType_x3f_1804_ = lean_ctor_get(v_info_1777_, 3);
lean_inc(v_expectedType_x3f_1804_);
lean_inc_ref(v_ctx_1776_);
v___f_1805_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1805_, 0, v_ctx_1776_);
lean_closure_set(v___f_1805_, 1, v_lctx_1803_);
lean_closure_set(v___f_1805_, 2, v_stx_1802_);
lean_closure_set(v___f_1805_, 3, v_expectedType_x3f_1804_);
lean_closure_set(v___f_1805_, 4, v_info_1777_);
v___x_1806_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1776_, v_lctx_1803_, v___f_1805_);
return v___x_1806_;
}
default: 
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_1808_ = l_Lean_Elab_CompletionInfo_stx(v_info_1777_);
lean_dec_ref(v_info_1777_);
v___x_1809_ = lean_box(0);
v___x_1810_ = 0;
lean_inc(v___x_1808_);
v___x_1811_ = l_Lean_Syntax_formatStx(v___x_1808_, v___x_1809_, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1807_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1776_, v___x_1808_);
lean_dec(v___x_1808_);
v___x_1816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_1818_, lean_object* v_info_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1818_, v_info_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_1825_, lean_object* v_info_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_1829_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1825_, v_info_1826_);
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_1832_, lean_object* v_info_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Elab_CommandInfo_format(v_ctx_1832_, v_info_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_1839_, lean_object* v_info_1840_){
_start:
{
lean_object* v_stx_1842_; lean_object* v_optionName_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_stx_1842_ = lean_ctor_get(v_info_1840_, 0);
lean_inc(v_stx_1842_);
v_optionName_1843_ = lean_ctor_get(v_info_1840_, 1);
lean_inc(v_optionName_1843_);
lean_dec_ref(v_info_1840_);
v___x_1844_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_1845_ = 1;
v___x_1846_ = l_Lean_Name_toString(v_optionName_1843_, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1844_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1839_, v_stx_1842_);
lean_dec(v_stx_1842_);
v___x_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_1854_, lean_object* v_info_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Elab_OptionInfo_format(v_ctx_1854_, v_info_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_1861_, lean_object* v_info_1862_){
_start:
{
lean_object* v_stx_1864_; lean_object* v_errorName_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1881_; 
v_stx_1864_ = lean_ctor_get(v_info_1862_, 0);
v_errorName_1865_ = lean_ctor_get(v_info_1862_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_info_1862_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1867_ = v_info_1862_;
v_isShared_1868_ = v_isSharedCheck_1881_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_errorName_1865_);
lean_inc(v_stx_1864_);
lean_dec(v_info_1862_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1881_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1869_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_1870_ = 1;
v___x_1871_ = l_Lean_Name_toString(v_errorName_1865_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 5);
lean_ctor_set(v___x_1867_, 1, v___x_1872_);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1874_ = v___x_1867_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1861_, v_stx_1864_);
lean_dec(v_stx_1864_);
v___x_1878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_1882_, lean_object* v_info_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1882_, v_info_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1892_, lean_object* v_fieldName_1893_, lean_object* v_ctx_1894_, lean_object* v_stx_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc_ref(v_val_1892_);
v___x_1901_ = lean_infer_type(v_val_1892_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l_Lean_Meta_ppExpr(v_a_1902_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1934_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1934_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1934_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Meta_ppExpr(v_val_1892_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1933_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1933_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1933_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1913_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1914_ = 1;
v___x_1915_ = l_Lean_Name_toString(v_fieldName_1893_, v___x_1914_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 3);
lean_ctor_set(v___x_1906_, 0, v___x_1915_);
v___x_1917_ = v___x_1906_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1913_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v_a_1904_);
v___x_1922_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_a_1909_);
v___x_1925_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1894_, v_stx_1895_);
v___x_1928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1928_);
v___x_1930_ = v___x_1911_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_del_object(v___x_1906_);
lean_dec(v_a_1904_);
lean_dec_ref(v_ctx_1894_);
lean_dec(v_fieldName_1893_);
return v___x_1908_;
}
}
}
else
{
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_ctx_1894_);
lean_dec(v_fieldName_1893_);
lean_dec_ref(v_val_1892_);
return v___x_1903_;
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_ctx_1894_);
lean_dec(v_fieldName_1893_);
lean_dec_ref(v_val_1892_);
v_a_1935_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1901_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1901_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1943_, lean_object* v_fieldName_1944_, lean_object* v_ctx_1945_, lean_object* v_stx_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1943_, v_fieldName_1944_, v_ctx_1945_, v_stx_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v_stx_1946_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1953_, lean_object* v_info_1954_){
_start:
{
lean_object* v_fieldName_1956_; lean_object* v_lctx_1957_; lean_object* v_val_1958_; lean_object* v_stx_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; 
v_fieldName_1956_ = lean_ctor_get(v_info_1954_, 1);
lean_inc(v_fieldName_1956_);
v_lctx_1957_ = lean_ctor_get(v_info_1954_, 2);
lean_inc_ref(v_lctx_1957_);
v_val_1958_ = lean_ctor_get(v_info_1954_, 3);
lean_inc_ref(v_val_1958_);
v_stx_1959_ = lean_ctor_get(v_info_1954_, 4);
lean_inc(v_stx_1959_);
lean_dec_ref(v_info_1954_);
lean_inc_ref(v_ctx_1953_);
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1960_, 0, v_val_1958_);
lean_closure_set(v___f_1960_, 1, v_fieldName_1956_);
lean_closure_set(v___f_1960_, 2, v_ctx_1953_);
lean_closure_set(v___f_1960_, 3, v_stx_1959_);
v___x_1961_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1953_, v_lctx_1957_, v___f_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1962_, lean_object* v_info_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Elab_FieldInfo_format(v_ctx_1962_, v_info_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
if (lean_obj_tag(v_x_1968_) == 0)
{
lean_dec(v_pre_1966_);
return v_x_1967_;
}
else
{
lean_object* v_head_1969_; lean_object* v_tail_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
v_head_1969_ = lean_ctor_get(v_x_1968_, 0);
v_tail_1970_ = lean_ctor_get(v_x_1968_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_x_1968_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v_x_1968_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_tail_1970_);
lean_inc(v_head_1969_);
lean_dec(v_x_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
lean_inc(v_pre_1966_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 5);
lean_ctor_set(v___x_1972_, 1, v_pre_1966_);
lean_ctor_set(v___x_1972_, 0, v_x_1967_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_x_1967_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_pre_1966_);
v___x_1975_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_head_1969_);
v_x_1967_ = v___x_1976_;
v_x_1968_ = v_tail_1970_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
lean_object* v___x_1982_; 
lean_dec(v_pre_1980_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
else
{
lean_object* v_head_1983_; lean_object* v_tail_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_head_1983_ = lean_ctor_get(v_x_1981_, 0);
v_tail_1984_ = lean_ctor_get(v_x_1981_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1981_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1986_ = v_x_1981_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_tail_1984_);
lean_inc(v_head_1983_);
lean_dec(v_x_1981_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
lean_inc(v_pre_1980_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 5);
lean_ctor_set(v___x_1986_, 1, v_head_1983_);
lean_ctor_set(v___x_1986_, 0, v_pre_1980_);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_pre_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_head_1983_);
v___x_1989_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1980_, v___x_1989_, v_tail_1984_);
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
if (lean_obj_tag(v_x_1993_) == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = l_List_reverse___redArg(v_x_1994_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
else
{
lean_object* v_head_2002_; lean_object* v_tail_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2021_; 
v_head_2002_ = lean_ctor_get(v_x_1993_, 0);
v_tail_2003_ = lean_ctor_get(v_x_1993_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_x_1993_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2005_ = v_x_1993_;
v_isShared_2006_ = v_isSharedCheck_2021_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_tail_2003_);
lean_inc(v_head_2002_);
lean_dec(v_x_1993_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2021_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_ppGoal(v_head_2002_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v_head_2002_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v_x_1994_);
lean_ctor_set(v___x_2005_, 0, v_a_2008_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2008_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_x_1994_);
v___x_2010_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
v_x_1993_ = v_tail_2003_;
v_x_1994_ = v___x_2010_;
goto _start;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_2005_);
lean_dec(v_tail_2003_);
lean_dec(v_x_1994_);
v_a_2013_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2007_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2007_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_2022_, v_x_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_2033_, lean_object* v___x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_2033_, v___x_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2046_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2045_, v_a_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2040_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2040_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_2059_, lean_object* v___x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_2059_, v___x_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2066_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(32u);
v___x_2071_ = lean_mk_empty_array_with_capacity(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2073_ = ((size_t)5ULL);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_unsigned_to_nat(32u);
v___x_2076_ = lean_mk_empty_array_with_capacity(v___x_2075_);
v___x_2077_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2078_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
lean_ctor_set(v___x_2078_, 2, v___x_2074_);
lean_ctor_set(v___x_2078_, 3, v___x_2074_);
lean_ctor_set_usize(v___x_2078_, 4, v___x_2073_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2079_ = lean_box(1);
v___x_2080_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2081_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_2082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2080_);
lean_ctor_set(v___x_2082_, 2, v___x_2079_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_2086_, lean_object* v_goals_2087_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_List_isEmpty___redArg(v_goals_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; 
v___x_2090_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_2091_ = lean_box(0);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2092_, 0, v_goals_2087_);
lean_closure_set(v___f_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_2086_, v___x_2090_, v___f_2092_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_goals_2087_);
lean_dec_ref(v_ctx_2086_);
v___x_2094_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_2096_, lean_object* v_goals_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_2096_, v_goals_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_2109_, lean_object* v_info_2110_){
_start:
{
lean_object* v_toCommandContextInfo_2112_; lean_object* v_parentDecl_x3f_2113_; lean_object* v_autoImplicits_2114_; lean_object* v_env_2115_; lean_object* v_cmdEnv_x3f_2116_; lean_object* v_fileMap_2117_; lean_object* v_options_2118_; lean_object* v_currNamespace_2119_; lean_object* v_openDecls_2120_; lean_object* v_ngen_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2163_; 
v_toCommandContextInfo_2112_ = lean_ctor_get(v_ctx_2109_, 0);
lean_inc_ref(v_toCommandContextInfo_2112_);
v_parentDecl_x3f_2113_ = lean_ctor_get(v_ctx_2109_, 1);
v_autoImplicits_2114_ = lean_ctor_get(v_ctx_2109_, 2);
v_env_2115_ = lean_ctor_get(v_toCommandContextInfo_2112_, 0);
v_cmdEnv_x3f_2116_ = lean_ctor_get(v_toCommandContextInfo_2112_, 1);
v_fileMap_2117_ = lean_ctor_get(v_toCommandContextInfo_2112_, 2);
v_options_2118_ = lean_ctor_get(v_toCommandContextInfo_2112_, 4);
v_currNamespace_2119_ = lean_ctor_get(v_toCommandContextInfo_2112_, 5);
v_openDecls_2120_ = lean_ctor_get(v_toCommandContextInfo_2112_, 6);
v_ngen_2121_ = lean_ctor_get(v_toCommandContextInfo_2112_, 7);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_toCommandContextInfo_2112_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v_toCommandContextInfo_2112_, 3);
lean_dec(v_unused_2164_);
v___x_2123_ = v_toCommandContextInfo_2112_;
v_isShared_2124_ = v_isSharedCheck_2163_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_ngen_2121_);
lean_inc(v_openDecls_2120_);
lean_inc(v_currNamespace_2119_);
lean_inc(v_options_2118_);
lean_inc(v_fileMap_2117_);
lean_inc(v_cmdEnv_x3f_2116_);
lean_inc(v_env_2115_);
lean_dec(v_toCommandContextInfo_2112_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2163_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_toElabInfo_2125_; lean_object* v_mctxBefore_2126_; lean_object* v_goalsBefore_2127_; lean_object* v_mctxAfter_2128_; lean_object* v_goalsAfter_2129_; lean_object* v___x_2131_; 
v_toElabInfo_2125_ = lean_ctor_get(v_info_2110_, 0);
lean_inc_ref(v_toElabInfo_2125_);
v_mctxBefore_2126_ = lean_ctor_get(v_info_2110_, 1);
lean_inc_ref(v_mctxBefore_2126_);
v_goalsBefore_2127_ = lean_ctor_get(v_info_2110_, 2);
lean_inc(v_goalsBefore_2127_);
v_mctxAfter_2128_ = lean_ctor_get(v_info_2110_, 3);
lean_inc_ref(v_mctxAfter_2128_);
v_goalsAfter_2129_ = lean_ctor_get(v_info_2110_, 4);
lean_inc(v_goalsAfter_2129_);
lean_dec_ref(v_info_2110_);
lean_inc_ref(v_ngen_2121_);
lean_inc(v_openDecls_2120_);
lean_inc(v_currNamespace_2119_);
lean_inc_ref(v_options_2118_);
lean_inc_ref(v_fileMap_2117_);
lean_inc(v_cmdEnv_x3f_2116_);
lean_inc_ref(v_env_2115_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 3, v_mctxBefore_2126_);
v___x_2131_ = v___x_2123_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_env_2115_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_cmdEnv_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_fileMap_2117_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_mctxBefore_2126_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_options_2118_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v_currNamespace_2119_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_openDecls_2120_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v_ngen_2121_);
v___x_2131_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v_ctxB_2132_; lean_object* v___x_2133_; 
lean_inc_ref(v_autoImplicits_2114_);
lean_inc(v_parentDecl_x3f_2113_);
v_ctxB_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_2132_, 0, v___x_2131_);
lean_ctor_set(v_ctxB_2132_, 1, v_parentDecl_x3f_2113_);
lean_ctor_set(v_ctxB_2132_, 2, v_autoImplicits_2114_);
v___x_2133_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_2132_, v_goalsBefore_2127_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v_ctxA_2136_; lean_object* v___x_2137_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2135_, 0, v_env_2115_);
lean_ctor_set(v___x_2135_, 1, v_cmdEnv_x3f_2116_);
lean_ctor_set(v___x_2135_, 2, v_fileMap_2117_);
lean_ctor_set(v___x_2135_, 3, v_mctxAfter_2128_);
lean_ctor_set(v___x_2135_, 4, v_options_2118_);
lean_ctor_set(v___x_2135_, 5, v_currNamespace_2119_);
lean_ctor_set(v___x_2135_, 6, v_openDecls_2120_);
lean_ctor_set(v___x_2135_, 7, v_ngen_2121_);
lean_inc_ref(v_autoImplicits_2114_);
lean_inc(v_parentDecl_x3f_2113_);
v_ctxA_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_2136_, 0, v___x_2135_);
lean_ctor_set(v_ctxA_2136_, 1, v_parentDecl_x3f_2113_);
lean_ctor_set(v_ctxA_2136_, 2, v_autoImplicits_2114_);
v___x_2137_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_2136_, v_goalsAfter_2129_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2161_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2161_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2161_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_stx_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v_stx_2142_ = lean_ctor_get(v_toElabInfo_2125_, 1);
lean_inc(v_stx_2142_);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_2144_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2109_, v_toElabInfo_2125_);
v___x_2145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_box(0);
v___x_2149_ = 0;
v___x_2150_ = l_Lean_Syntax_formatStx(v_stx_2142_, v___x_2148_, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2147_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v_a_2134_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_2156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v_a_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2157_);
v___x_2159_ = v___x_2140_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_dec(v_a_2134_);
lean_dec_ref(v_toElabInfo_2125_);
lean_dec_ref(v_ctx_2109_);
return v___x_2137_;
}
}
else
{
lean_dec(v_goalsAfter_2129_);
lean_dec_ref(v_mctxAfter_2128_);
lean_dec_ref(v_toElabInfo_2125_);
lean_dec_ref(v_ngen_2121_);
lean_dec(v_openDecls_2120_);
lean_dec(v_currNamespace_2119_);
lean_dec_ref(v_options_2118_);
lean_dec_ref(v_fileMap_2117_);
lean_dec(v_cmdEnv_x3f_2116_);
lean_dec_ref(v_env_2115_);
lean_dec_ref(v_ctx_2109_);
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_2165_, lean_object* v_info_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Elab_TacticInfo_format(v_ctx_2165_, v_info_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_2175_, lean_object* v_info_2176_){
_start:
{
lean_object* v_lctx_2178_; lean_object* v_stx_2179_; lean_object* v_output_2180_; lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v___x_2183_; lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2196_; 
v_lctx_2178_ = lean_ctor_get(v_info_2176_, 0);
lean_inc_ref_n(v_lctx_2178_, 2);
v_stx_2179_ = lean_ctor_get(v_info_2176_, 1);
lean_inc(v_stx_2179_);
v_output_2180_ = lean_ctor_get(v_info_2176_, 2);
lean_inc(v_output_2180_);
lean_dec_ref(v_info_2176_);
v___x_2181_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2175_, v_lctx_2178_, v_stx_2179_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2175_, v_lctx_2178_, v_output_2180_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2188_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_a_2182_);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2192_);
v___x_2194_ = v___x_2186_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_2197_, lean_object* v_info_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2197_, v_info_2198_);
lean_dec_ref(v_ctx_2197_);
return v_res_2200_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_2204_; size_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = 1;
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_2207_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_ctor_set_usize(v___x_2207_, 2, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*3, v___x_2204_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_2211_){
_start:
{
lean_object* v_toWidgetInstance_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2241_; 
v_toWidgetInstance_2212_ = lean_ctor_get(v_info_2211_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_info_2211_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v_info_2211_, 1);
lean_dec(v_unused_2242_);
v___x_2214_ = v_info_2211_;
v_isShared_2215_ = v_isSharedCheck_2241_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_toWidgetInstance_2212_);
lean_dec(v_info_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2241_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_id_2216_; lean_object* v_props_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_fst_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2239_; 
v_id_2216_ = lean_ctor_get(v_toWidgetInstance_2212_, 0);
lean_inc(v_id_2216_);
v_props_2217_ = lean_ctor_get(v_toWidgetInstance_2212_, 1);
lean_inc_ref(v_props_2217_);
lean_dec_ref(v_toWidgetInstance_2212_);
v___x_2218_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_2219_ = lean_apply_1(v_props_2217_, v___x_2218_);
v_fst_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v___x_2219_, 1);
lean_dec(v_unused_2240_);
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2239_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_fst_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2239_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2224_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_2225_ = 1;
v___x_2226_ = l_Lean_Name_toString(v_id_2216_, v___x_2225_);
v___x_2227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set_tag(v___x_2222_, 5);
lean_ctor_set(v___x_2222_, 1, v___x_2227_);
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2229_ = v___x_2222_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2230_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 5);
lean_ctor_set(v___x_2214_, 1, v___x_2230_);
lean_ctor_set(v___x_2214_, 0, v___x_2229_);
v___x_2232_ = v___x_2214_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = lean_unsigned_to_nat(80u);
v___x_2234_ = l_Lean_Json_pretty(v_fst_2220_, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2232_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
return v___x_2236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_2249_){
_start:
{
lean_object* v_userName_2250_; lean_object* v_id_2251_; lean_object* v_baseId_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_userName_2250_ = lean_ctor_get(v_info_2249_, 0);
lean_inc(v_userName_2250_);
v_id_2251_ = lean_ctor_get(v_info_2249_, 1);
lean_inc(v_id_2251_);
v_baseId_2252_ = lean_ctor_get(v_info_2249_, 2);
lean_inc(v_baseId_2252_);
lean_dec_ref(v_info_2249_);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_2254_ = lean_erase_macro_scopes(v_userName_2250_);
v___x_2255_ = 1;
v___x_2256_ = l_Lean_Name_toString(v___x_2254_, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2253_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_Name_toString(v_id_2251_, v___x_2255_);
v___x_2262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2260_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_2265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = l_Lean_Name_toString(v_baseId_2252_, v___x_2255_);
v___x_2267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2265_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_2272_, lean_object* v_info_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_2275_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_2272_, v_info_2273_);
v___x_2276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_2277_, lean_object* v_info_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2277_, v_info_2278_);
lean_dec(v_info_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_2282_, lean_object* v_info_2283_){
_start:
{
lean_object* v_mkDocString_x3f_2285_; 
v_mkDocString_x3f_2285_ = lean_ctor_get(v_info_2283_, 2);
lean_inc(v_mkDocString_x3f_2285_);
lean_dec_ref(v_info_2283_);
if (lean_obj_tag(v_mkDocString_x3f_2285_) == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_ppCtx_2282_);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
else
{
lean_object* v_val_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2320_; 
v_val_2288_ = lean_ctor_get(v_mkDocString_x3f_2285_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_mkDocString_x3f_2285_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2290_ = v_mkDocString_x3f_2285_;
v_isShared_2291_ = v_isSharedCheck_2320_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_val_2288_);
lean_dec(v_mkDocString_x3f_2285_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2320_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_apply_2(v_val_2288_, v_ppCtx_2282_, lean_box(0));
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2303_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2303_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2303_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_a_2293_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2300_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2319_; 
v_a_2304_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2306_ = v___x_2292_;
v_isShared_2307_ = v_isSharedCheck_2319_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2292_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2319_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2308_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_2309_ = lean_io_error_to_string(v_a_2304_);
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2312_);
v___x_2314_ = v___x_2290_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2316_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2314_);
v___x_2316_ = v___x_2306_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_2321_, lean_object* v_info_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_2321_, v_info_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
if (lean_obj_tag(v_x_2325_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2327_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2339_; 
v_val_2328_ = lean_ctor_get(v_x_2325_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_2325_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2330_ = v_x_2325_;
v_isShared_2331_ = v_isSharedCheck_2339_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_val_2328_);
lean_dec(v_x_2325_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2339_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2332_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2333_ = l_String_quote(v_val_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 3);
lean_ctor_set(v___x_2330_, 0, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2332_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Repr_addAppParen(v___x_2336_, v_x_2326_);
return v___x_2337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2340_, v_x_2341_);
lean_dec(v_x_2341_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2357_, lean_object* v_info_2358_){
_start:
{
lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v_toTermInfo_2366_; lean_object* v_location_x3f_2367_; uint8_t v_explicit_2368_; lean_object* v___y_2370_; 
v_toTermInfo_2366_ = lean_ctor_get(v_info_2358_, 0);
lean_inc_ref(v_toTermInfo_2366_);
v_location_x3f_2367_ = lean_ctor_get(v_info_2358_, 1);
lean_inc(v_location_x3f_2367_);
v_explicit_2368_ = lean_ctor_get_uint8(v_info_2358_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_2367_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2452_; 
v_val_2391_ = lean_ctor_get(v_location_x3f_2367_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_location_x3f_2367_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2393_ = v_location_x3f_2367_;
v_isShared_2394_ = v_isSharedCheck_2452_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_location_x3f_2367_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2452_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_range_2395_; lean_object* v_pos_2396_; lean_object* v_endPos_2397_; lean_object* v_module_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2450_; 
v_range_2395_ = lean_ctor_get(v_val_2391_, 1);
v_pos_2396_ = lean_ctor_get(v_range_2395_, 0);
lean_inc_ref(v_pos_2396_);
v_endPos_2397_ = lean_ctor_get(v_range_2395_, 2);
lean_inc_ref(v_endPos_2397_);
v_module_2398_ = lean_ctor_get(v_val_2391_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_val_2391_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v_val_2391_, 1);
lean_dec(v_unused_2451_);
v___x_2400_ = v_val_2391_;
v_isShared_2401_ = v_isSharedCheck_2450_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_module_2398_);
lean_dec(v_val_2391_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2450_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_line_2402_; lean_object* v_column_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2449_; 
v_line_2402_ = lean_ctor_get(v_pos_2396_, 0);
v_column_2403_ = lean_ctor_get(v_pos_2396_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_pos_2396_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2405_ = v_pos_2396_;
v_isShared_2406_ = v_isSharedCheck_2449_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_column_2403_);
lean_inc(v_line_2402_);
lean_dec(v_pos_2396_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2449_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v_line_2407_; lean_object* v_column_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2448_; 
v_line_2407_ = lean_ctor_get(v_endPos_2397_, 0);
v_column_2408_ = lean_ctor_get(v_endPos_2397_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_endPos_2397_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2410_ = v_endPos_2397_;
v_isShared_2411_ = v_isSharedCheck_2448_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_column_2408_);
lean_inc(v_line_2407_);
lean_dec(v_endPos_2397_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2448_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2412_ = 1;
v___x_2413_ = l_Lean_Name_toString(v_module_2398_, v___x_2412_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 3);
lean_ctor_set(v___x_2393_, 0, v___x_2413_);
v___x_2415_ = v___x_2393_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 5);
lean_ctor_set(v___x_2410_, 1, v___x_2416_);
lean_ctor_set(v___x_2410_, 0, v___x_2415_);
v___x_2418_ = v___x_2410_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2420_ = l_Nat_reprFast(v_line_2402_);
v___x_2421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 5);
lean_ctor_set(v___x_2405_, 1, v___x_2421_);
lean_ctor_set(v___x_2405_, 0, v___x_2419_);
v___x_2423_ = v___x_2405_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 5);
lean_ctor_set(v___x_2400_, 1, v___x_2424_);
lean_ctor_set(v___x_2400_, 0, v___x_2423_);
v___x_2426_ = v___x_2400_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2427_ = l_Nat_reprFast(v_column_2403_);
v___x_2428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2426_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2418_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Nat_reprFast(v_line_2407_);
v___x_2436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2419_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2424_);
v___x_2439_ = l_Nat_reprFast(v_column_2408_);
v___x_2440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2438_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___x_2430_);
v___x_2443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2434_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___y_2370_ = v___x_2443_;
goto v___jp_2369_;
}
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
lean_object* v___x_2453_; 
lean_dec(v_location_x3f_2367_);
v___x_2453_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2370_ = v___x_2453_;
goto v___jp_2369_;
}
v___jp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_inc_ref(v___y_2362_);
v___x_2363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___y_2362_);
v___x_2364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___y_2361_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
v___jp_2369_:
{
lean_object* v_lctx_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v_a_2374_; lean_object* v___x_2375_; 
v_lctx_2371_ = lean_ctor_get(v_toTermInfo_2366_, 1);
lean_inc_ref(v_lctx_2371_);
v___x_2372_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_2357_, v_lctx_2371_);
v___x_2373_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_2372_, v_info_2358_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = l_Lean_Elab_TermInfo_format(v_ctx_2357_, v_toTermInfo_2366_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v_a_2376_);
v___x_2379_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___y_2370_);
v___x_2382_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_2374_, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2383_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
if (v_explicit_2368_ == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2361_ = v___x_2388_;
v___y_2362_ = v___x_2389_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2390_; 
v___x_2390_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2361_ = v___x_2388_;
v___y_2362_ = v___x_2390_;
goto v___jp_2360_;
}
}
else
{
lean_dec(v_a_2374_);
lean_dec(v___y_2370_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2454_, lean_object* v_info_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2454_, v_info_2455_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2461_, lean_object* v_info_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2464_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2461_, v_info_2462_);
v___x_2465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2469_, lean_object* v_info_2470_){
_start:
{
lean_object* v_stx_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_stx_2471_ = lean_ctor_get(v_info_2470_, 1);
v___x_2472_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2471_);
v___x_2473_ = l_Lean_Syntax_getKind(v_stx_2471_);
v___x_2474_ = 1;
v___x_2475_ = l_Lean_Name_toString(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2472_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2469_, v_info_2470_);
v___x_2481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2491_, lean_object* v_info_2492_){
_start:
{
lean_object* v_toElabInfo_2493_; lean_object* v_name_2494_; uint8_t v_kind_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_toElabInfo_2493_ = lean_ctor_get(v_info_2492_, 0);
lean_inc_ref(v_toElabInfo_2493_);
v_name_2494_ = lean_ctor_get(v_info_2492_, 1);
lean_inc(v_name_2494_);
v_kind_2495_ = lean_ctor_get_uint8(v_info_2492_, sizeof(void*)*2);
lean_dec_ref(v_info_2492_);
v___x_2496_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2497_ = 1;
v___x_2498_ = l_Lean_Name_toString(v_name_2494_, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2496_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2495_, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2502_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2491_, v_toElabInfo_2493_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2510_, lean_object* v_x_2511_){
_start:
{
switch(lean_obj_tag(v_x_2511_))
{
case 0:
{
lean_object* v_i_2513_; lean_object* v___x_2514_; 
v_i_2513_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2513_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2514_ = l_Lean_Elab_TacticInfo_format(v_ctx_2510_, v_i_2513_);
return v___x_2514_;
}
case 1:
{
lean_object* v_i_2515_; lean_object* v___x_2516_; 
v_i_2515_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2515_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2516_ = l_Lean_Elab_TermInfo_format(v_ctx_2510_, v_i_2515_);
return v___x_2516_;
}
case 2:
{
lean_object* v_i_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2525_; 
v_i_2517_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2519_ = v_x_2511_;
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_i_2517_);
lean_dec(v_x_2511_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2510_, v_i_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
case 3:
{
lean_object* v_i_2526_; lean_object* v___x_2527_; 
v_i_2526_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2526_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2527_ = l_Lean_Elab_CommandInfo_format(v_ctx_2510_, v_i_2526_);
return v___x_2527_;
}
case 4:
{
lean_object* v_i_2528_; lean_object* v___x_2529_; 
v_i_2528_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2528_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2529_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2510_, v_i_2528_);
lean_dec_ref(v_ctx_2510_);
return v___x_2529_;
}
case 5:
{
lean_object* v_i_2530_; lean_object* v___x_2531_; 
v_i_2530_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2530_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2531_ = l_Lean_Elab_OptionInfo_format(v_ctx_2510_, v_i_2530_);
return v___x_2531_;
}
case 6:
{
lean_object* v_i_2532_; lean_object* v___x_2533_; 
v_i_2532_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2532_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2533_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2510_, v_i_2532_);
return v___x_2533_;
}
case 7:
{
lean_object* v_i_2534_; lean_object* v___x_2535_; 
v_i_2534_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2534_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2535_ = l_Lean_Elab_FieldInfo_format(v_ctx_2510_, v_i_2534_);
return v___x_2535_;
}
case 8:
{
lean_object* v_i_2536_; lean_object* v___x_2537_; 
v_i_2536_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2536_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2537_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2510_, v_i_2536_);
return v___x_2537_;
}
case 9:
{
lean_object* v_i_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v_ctx_2510_);
v_i_2538_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v_x_2511_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_i_2538_);
lean_dec(v_x_2511_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
case 10:
{
lean_object* v_i_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v_ctx_2510_);
v_i_2547_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2549_ = v_x_2511_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_i_2547_);
lean_dec(v_x_2511_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = l_Lean_Elab_CustomInfo_format(v_i_2547_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set_tag(v___x_2549_, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
case 11:
{
lean_object* v_i_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_ctx_2510_);
v_i_2556_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v_x_2511_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_i_2556_);
lean_dec(v_x_2511_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
case 12:
{
lean_object* v_i_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_i_2565_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2567_ = v_x_2511_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_i_2565_);
lean_dec(v_x_2511_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2510_, v_i_2565_);
lean_dec(v_i_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
case 13:
{
lean_object* v_i_2574_; lean_object* v___x_2575_; 
v_i_2574_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_ref(v_i_2574_);
lean_dec_ref_known(v_x_2511_, 1);
v___x_2575_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2510_, v_i_2574_);
return v___x_2575_;
}
case 14:
{
lean_object* v_i_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2584_; 
v_i_2576_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2578_ = v_x_2511_;
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_i_2576_);
lean_dec(v_x_2511_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2510_, v_i_2576_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2580_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
case 15:
{
lean_object* v_i_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_i_2585_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v_x_2511_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_i_2585_);
lean_dec(v_x_2511_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = l_Lean_Elab_DocInfo_format(v_ctx_2510_, v_i_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
default: 
{
lean_object* v_i_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
v_i_2594_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2596_ = v_x_2511_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_i_2594_);
lean_dec(v_x_2511_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2510_, v_i_2594_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2603_, lean_object* v_x_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Elab_Info_format(v_ctx_2603_, v_x_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2607_){
_start:
{
switch(lean_obj_tag(v_x_2607_))
{
case 0:
{
lean_object* v_i_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2616_; 
v_i_2608_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2610_ = v_x_2607_;
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_i_2608_);
lean_dec(v_x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_toElabInfo_2612_; lean_object* v___x_2614_; 
v_toElabInfo_2612_ = lean_ctor_get(v_i_2608_, 0);
lean_inc_ref(v_toElabInfo_2612_);
lean_dec_ref(v_i_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 1);
lean_ctor_set(v___x_2610_, 0, v_toElabInfo_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_toElabInfo_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
case 1:
{
lean_object* v_i_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_i_2617_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v_x_2607_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_i_2617_);
lean_dec(v_x_2607_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_toElabInfo_2621_; lean_object* v___x_2623_; 
v_toElabInfo_2621_ = lean_ctor_get(v_i_2617_, 0);
lean_inc_ref(v_toElabInfo_2621_);
lean_dec_ref(v_i_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v_toElabInfo_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_toElabInfo_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
case 2:
{
lean_object* v_i_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2634_; 
v_i_2626_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2628_ = v_x_2607_;
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_i_2626_);
lean_dec(v_x_2607_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_toElabInfo_2630_; lean_object* v___x_2632_; 
v_toElabInfo_2630_ = lean_ctor_get(v_i_2626_, 0);
lean_inc_ref(v_toElabInfo_2630_);
lean_dec_ref(v_i_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 1);
lean_ctor_set(v___x_2628_, 0, v_toElabInfo_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_toElabInfo_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
case 3:
{
lean_object* v_i_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_i_2635_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v_x_2607_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_i_2635_);
lean_dec(v_x_2607_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_i_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
case 13:
{
lean_object* v_i_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2652_; 
v_i_2643_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2645_ = v_x_2607_;
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_i_2643_);
lean_dec(v_x_2607_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_toTermInfo_2647_; lean_object* v_toElabInfo_2648_; lean_object* v___x_2650_; 
v_toTermInfo_2647_ = lean_ctor_get(v_i_2643_, 0);
lean_inc_ref(v_toTermInfo_2647_);
lean_dec_ref(v_i_2643_);
v_toElabInfo_2648_ = lean_ctor_get(v_toTermInfo_2647_, 0);
lean_inc_ref(v_toElabInfo_2648_);
lean_dec_ref(v_toTermInfo_2647_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 1);
lean_ctor_set(v___x_2645_, 0, v_toElabInfo_2648_);
v___x_2650_ = v___x_2645_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_toElabInfo_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
case 14:
{
lean_object* v_i_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_i_2653_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v_x_2607_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_i_2653_);
lean_dec(v_x_2607_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_i_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
case 15:
{
lean_object* v_i_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_i_2661_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v_x_2607_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_i_2661_);
lean_dec(v_x_2607_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 1);
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_i_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
case 16:
{
lean_object* v_i_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2677_; 
v_i_2669_ = lean_ctor_get(v_x_2607_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2671_ = v_x_2607_;
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_i_2669_);
lean_dec(v_x_2607_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_toElabInfo_2673_; lean_object* v___x_2675_; 
v_toElabInfo_2673_ = lean_ctor_get(v_i_2669_, 0);
lean_inc_ref(v_toElabInfo_2673_);
lean_dec_ref(v_i_2669_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 1);
lean_ctor_set(v___x_2671_, 0, v_toElabInfo_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_toElabInfo_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
default: 
{
lean_object* v___x_2678_; 
lean_dec_ref(v_x_2607_);
v___x_2678_ = lean_box(0);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
if (lean_obj_tag(v_x_2679_) == 1)
{
if (lean_obj_tag(v_x_2680_) == 0)
{
lean_object* v_val_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2716_; 
v_val_2681_ = lean_ctor_get(v_x_2679_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_x_2679_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2683_ = v_x_2679_;
v_isShared_2684_ = v_isSharedCheck_2716_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_val_2681_);
lean_dec(v_x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2716_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_toCommandContextInfo_2685_; lean_object* v_i_2686_; lean_object* v_parentDecl_x3f_2687_; lean_object* v_autoImplicits_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2714_; 
v_toCommandContextInfo_2685_ = lean_ctor_get(v_val_2681_, 0);
lean_inc_ref(v_toCommandContextInfo_2685_);
v_i_2686_ = lean_ctor_get(v_x_2680_, 0);
v_parentDecl_x3f_2687_ = lean_ctor_get(v_val_2681_, 1);
v_autoImplicits_2688_ = lean_ctor_get(v_val_2681_, 2);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_val_2681_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_val_2681_, 0);
lean_dec(v_unused_2715_);
v___x_2690_ = v_val_2681_;
v_isShared_2691_ = v_isSharedCheck_2714_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_autoImplicits_2688_);
lean_inc(v_parentDecl_x3f_2687_);
lean_dec(v_val_2681_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2714_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_env_2692_; lean_object* v_cmdEnv_x3f_2693_; lean_object* v_fileMap_2694_; lean_object* v_options_2695_; lean_object* v_currNamespace_2696_; lean_object* v_openDecls_2697_; lean_object* v_ngen_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2712_; 
v_env_2692_ = lean_ctor_get(v_toCommandContextInfo_2685_, 0);
v_cmdEnv_x3f_2693_ = lean_ctor_get(v_toCommandContextInfo_2685_, 1);
v_fileMap_2694_ = lean_ctor_get(v_toCommandContextInfo_2685_, 2);
v_options_2695_ = lean_ctor_get(v_toCommandContextInfo_2685_, 4);
v_currNamespace_2696_ = lean_ctor_get(v_toCommandContextInfo_2685_, 5);
v_openDecls_2697_ = lean_ctor_get(v_toCommandContextInfo_2685_, 6);
v_ngen_2698_ = lean_ctor_get(v_toCommandContextInfo_2685_, 7);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_toCommandContextInfo_2685_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v_toCommandContextInfo_2685_, 3);
lean_dec(v_unused_2713_);
v___x_2700_ = v_toCommandContextInfo_2685_;
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_ngen_2698_);
lean_inc(v_openDecls_2697_);
lean_inc(v_currNamespace_2696_);
lean_inc(v_options_2695_);
lean_inc(v_fileMap_2694_);
lean_inc(v_cmdEnv_x3f_2693_);
lean_inc(v_env_2692_);
lean_dec(v_toCommandContextInfo_2685_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_mctxAfter_2702_; lean_object* v___x_2704_; 
v_mctxAfter_2702_ = lean_ctor_get(v_i_2686_, 3);
lean_inc_ref(v_mctxAfter_2702_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 3, v_mctxAfter_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_env_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_cmdEnv_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_fileMap_2694_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_mctxAfter_2702_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_options_2695_);
lean_ctor_set(v_reuseFailAlloc_2711_, 5, v_currNamespace_2696_);
lean_ctor_set(v_reuseFailAlloc_2711_, 6, v_openDecls_2697_);
lean_ctor_set(v_reuseFailAlloc_2711_, 7, v_ngen_2698_);
v___x_2704_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2704_);
v___x_2706_ = v___x_2690_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_parentDecl_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_autoImplicits_2688_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2706_);
v___x_2708_ = v___x_2683_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
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
}
}
}
else
{
return v_x_2679_;
}
}
else
{
return v_x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2717_, lean_object* v_x_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2717_, v_x_2718_);
lean_dec_ref(v_x_2718_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2720_, lean_object* v_x_2721_){
_start:
{
if (lean_obj_tag(v_x_2721_) == 0)
{
return v_x_2720_;
}
else
{
lean_object* v_head_2722_; lean_object* v_tail_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_head_2722_ = lean_ctor_get(v_x_2721_, 0);
v_tail_2723_ = lean_ctor_get(v_x_2721_, 1);
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2725_ = lean_string_append(v_x_2720_, v___x_2724_);
v___x_2726_ = lean_expr_dbg_to_string(v_head_2722_);
v___x_2727_ = lean_string_append(v___x_2725_, v___x_2726_);
lean_dec_ref(v___x_2726_);
v_x_2720_ = v___x_2727_;
v_x_2721_ = v_tail_2723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2729_, v_x_2730_);
lean_dec(v_x_2730_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2734_){
_start:
{
if (lean_obj_tag(v_x_2734_) == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2735_;
}
else
{
lean_object* v_tail_2736_; 
v_tail_2736_ = lean_ctor_get(v_x_2734_, 1);
if (lean_obj_tag(v_tail_2736_) == 0)
{
lean_object* v_head_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_head_2737_ = lean_ctor_get(v_x_2734_, 0);
v___x_2738_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2739_ = lean_expr_dbg_to_string(v_head_2737_);
v___x_2740_ = lean_string_append(v___x_2738_, v___x_2739_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
return v___x_2742_;
}
else
{
lean_object* v_head_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint32_t v___x_2748_; lean_object* v___x_2749_; 
v_head_2743_ = lean_ctor_get(v_x_2734_, 0);
v___x_2744_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2745_ = lean_expr_dbg_to_string(v_head_2743_);
v___x_2746_ = lean_string_append(v___x_2744_, v___x_2745_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2746_, v_tail_2736_);
v___x_2748_ = 93;
v___x_2749_ = lean_string_push(v___x_2747_, v___x_2748_);
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2750_);
lean_dec(v_x_2750_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2758_){
_start:
{
switch(lean_obj_tag(v_ctx_2758_))
{
case 0:
{
lean_object* v___x_2759_; 
lean_dec_ref_known(v_ctx_2758_, 1);
v___x_2759_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2759_;
}
case 1:
{
lean_object* v_parentDecl_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2773_; 
v_parentDecl_2760_ = lean_ctor_get(v_ctx_2758_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_ctx_2758_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2762_ = v_ctx_2758_;
v_isShared_2763_ = v_isSharedCheck_2773_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_parentDecl_2760_);
lean_dec(v_ctx_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2773_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2764_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2765_ = 1;
v___x_2766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2760_, v___x_2765_);
v___x_2767_ = lean_string_append(v___x_2764_, v___x_2766_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2769_ = lean_string_append(v___x_2767_, v___x_2768_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 3);
lean_ctor_set(v___x_2762_, 0, v___x_2769_);
v___x_2771_ = v___x_2762_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
default: 
{
lean_object* v_autoImplicits_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2789_; 
v_autoImplicits_2774_ = lean_ctor_get(v_ctx_2758_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_ctx_2758_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2776_ = v_ctx_2758_;
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_autoImplicits_2774_);
lean_dec(v_ctx_2758_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2778_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2779_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2780_ = lean_array_to_list(v_autoImplicits_2774_);
v___x_2781_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2780_);
lean_dec(v___x_2780_);
v___x_2782_ = lean_string_append(v___x_2779_, v___x_2781_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = lean_string_append(v___x_2778_, v___x_2782_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2785_ = lean_string_append(v___x_2783_, v___x_2784_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 3);
lean_ctor_set(v___x_2776_, 0, v___x_2785_);
v___x_2787_ = v___x_2776_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2799_, lean_object* v_ctx_x3f_2800_){
_start:
{
switch(lean_obj_tag(v_tree_2799_))
{
case 0:
{
lean_object* v_i_2802_; lean_object* v_t_2803_; lean_object* v___x_2804_; 
v_i_2802_ = lean_ctor_get(v_tree_2799_, 0);
lean_inc_ref(v_i_2802_);
v_t_2803_ = lean_ctor_get(v_tree_2799_, 1);
lean_inc_ref(v_t_2803_);
lean_dec_ref_known(v_tree_2799_, 2);
v___x_2804_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2802_, v_ctx_x3f_2800_);
v_tree_2799_ = v_t_2803_;
v_ctx_x3f_2800_ = v___x_2804_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2800_) == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec_ref_known(v_tree_2799_, 2);
v___x_2806_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
else
{
lean_object* v_i_2808_; lean_object* v_children_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2859_; 
v_i_2808_ = lean_ctor_get(v_tree_2799_, 0);
v_children_2809_ = lean_ctor_get(v_tree_2799_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_tree_2799_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2811_ = v_tree_2799_;
v_isShared_2812_ = v_isSharedCheck_2859_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_children_2809_);
lean_inc(v_i_2808_);
lean_dec(v_tree_2799_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2859_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_val_2813_; lean_object* v___x_2814_; 
v_val_2813_ = lean_ctor_get(v_ctx_x3f_2800_, 0);
lean_inc_ref(v_i_2808_);
lean_inc(v_val_2813_);
v___x_2814_ = l_Lean_Elab_Info_format(v_val_2813_, v_i_2808_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2858_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2858_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2858_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_size_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_size_2819_ = lean_ctor_get(v_children_2809_, 2);
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = lean_nat_dec_eq(v_size_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_del_object(v___x_2817_);
v___x_2822_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2800_, v_i_2808_);
lean_dec_ref(v_i_2808_);
v___x_2823_ = l_Lean_PersistentArray_toList___redArg(v_children_2809_);
lean_dec_ref(v_children_2809_);
v___x_2824_ = lean_box(0);
v___x_2825_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2822_, v___x_2823_, v___x_2824_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2841_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2841_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2841_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 5);
lean_ctor_set(v___x_2811_, 1, v_a_2815_);
lean_ctor_set(v___x_2811_, 0, v___x_2830_);
v___x_2832_ = v___x_2811_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_a_2815_);
v___x_2832_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2833_ = lean_box(1);
v___x_2834_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2833_, v_a_2826_);
v___x_2835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2832_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Std_Format_nestD(v___x_2835_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2836_);
v___x_2838_ = v___x_2828_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2815_);
lean_del_object(v___x_2811_);
v_a_2842_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2825_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2825_);
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
else
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_dec_ref(v_children_2809_);
lean_dec_ref_known(v_ctx_x3f_2800_, 1);
lean_dec_ref(v_i_2808_);
v___x_2850_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 5);
lean_ctor_set(v___x_2811_, 1, v_a_2815_);
lean_ctor_set(v___x_2811_, 0, v___x_2850_);
v___x_2852_ = v___x_2811_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_a_2815_);
v___x_2852_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = l_Std_Format_nestD(v___x_2852_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2853_);
v___x_2855_ = v___x_2817_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
else
{
lean_del_object(v___x_2811_);
lean_dec_ref(v_children_2809_);
lean_dec_ref_known(v_ctx_x3f_2800_, 1);
lean_dec_ref(v_i_2808_);
return v___x_2814_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_ctx_x3f_2800_);
v_mvarId_2860_ = lean_ctor_get(v_tree_2799_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_tree_2799_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2862_ = v_tree_2799_;
v_isShared_2863_ = v_isSharedCheck_2873_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_mvarId_2860_);
lean_dec(v_tree_2799_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2873_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2864_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2865_ = 1;
v___x_2866_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2860_, v___x_2865_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 3);
lean_ctor_set(v___x_2862_, 0, v___x_2866_);
v___x_2868_ = v___x_2862_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2864_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Std_Format_nestD(v___x_2869_);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec(v___x_2874_);
v___x_2878_ = l_List_reverse___redArg(v_x_2876_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v_head_2880_; lean_object* v_tail_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2899_; 
v_head_2880_ = lean_ctor_get(v_x_2875_, 0);
v_tail_2881_ = lean_ctor_get(v_x_2875_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2883_ = v_x_2875_;
v_isShared_2884_ = v_isSharedCheck_2899_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_tail_2881_);
lean_inc(v_head_2880_);
lean_dec(v_x_2875_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2899_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; 
lean_inc(v___x_2874_);
v___x_2885_ = l_Lean_Elab_InfoTree_format(v_head_2880_, v___x_2874_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 1, v_x_2876_);
lean_ctor_set(v___x_2883_, 0, v_a_2886_);
v___x_2888_ = v___x_2883_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2886_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_x_2876_);
v___x_2888_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
v_x_2875_ = v_tail_2881_;
v_x_2876_ = v___x_2888_;
goto _start;
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_del_object(v___x_2883_);
lean_dec(v_tail_2881_);
lean_dec(v_x_2876_);
lean_dec(v___x_2874_);
v_a_2891_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2885_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2885_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2900_, v_x_2901_, v_x_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2905_, lean_object* v_ctx_x3f_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Elab_InfoTree_format(v_tree_2905_, v_ctx_x3f_2906_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2909_, lean_object* v_s_2910_){
_start:
{
uint8_t v_enabled_2911_; lean_object* v_assignment_2912_; lean_object* v_lazyAssignment_2913_; lean_object* v_trees_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
v_enabled_2911_ = lean_ctor_get_uint8(v_s_2910_, sizeof(void*)*3);
v_assignment_2912_ = lean_ctor_get(v_s_2910_, 0);
v_lazyAssignment_2913_ = lean_ctor_get(v_s_2910_, 1);
v_trees_2914_ = lean_ctor_get(v_s_2910_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_s_2910_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2916_ = v_s_2910_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_trees_2914_);
lean_inc(v_lazyAssignment_2913_);
lean_inc(v_assignment_2912_);
lean_dec(v_s_2910_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = lean_apply_1(v_f_2909_, v_trees_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 2, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_assignment_2912_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_lazyAssignment_2913_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v___x_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*3, v_enabled_2911_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2923_, lean_object* v_f_2924_){
_start:
{
lean_object* v_modifyInfoState_2925_; lean_object* v___f_2926_; lean_object* v___x_2927_; 
v_modifyInfoState_2925_ = lean_ctor_get(v_inst_2923_, 1);
lean_inc(v_modifyInfoState_2925_);
lean_dec_ref(v_inst_2923_);
v___f_2926_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2926_, 0, v_f_2924_);
v___x_2927_ = lean_apply_1(v_modifyInfoState_2925_, v___f_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2928_, lean_object* v_inst_2929_, lean_object* v_f_2930_){
_start:
{
lean_object* v_modifyInfoState_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; 
v_modifyInfoState_2931_ = lean_ctor_get(v_inst_2929_, 1);
lean_inc(v_modifyInfoState_2931_);
lean_dec_ref(v_inst_2929_);
v___f_2932_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2932_, 0, v_f_2930_);
v___x_2933_ = lean_apply_1(v_modifyInfoState_2931_, v___f_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_unsigned_to_nat(32u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2937_ = ((size_t)5ULL);
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_2939_ = lean_unsigned_to_nat(32u);
v___x_2940_ = lean_mk_empty_array_with_capacity(v___x_2939_);
v___x_2941_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
lean_ctor_set(v___x_2942_, 2, v___x_2938_);
lean_ctor_set(v___x_2942_, 3, v___x_2938_);
lean_ctor_set_usize(v___x_2942_, 4, v___x_2937_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2943_){
_start:
{
uint8_t v_enabled_2944_; lean_object* v_assignment_2945_; lean_object* v_lazyAssignment_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2954_; 
v_enabled_2944_ = lean_ctor_get_uint8(v_s_2943_, sizeof(void*)*3);
v_assignment_2945_ = lean_ctor_get(v_s_2943_, 0);
v_lazyAssignment_2946_ = lean_ctor_get(v_s_2943_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_s_2943_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_s_2943_, 2);
lean_dec(v_unused_2955_);
v___x_2948_ = v_s_2943_;
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_lazyAssignment_2946_);
lean_inc(v_assignment_2945_);
lean_dec(v_s_2943_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 2, v___x_2950_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_assignment_2945_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_lazyAssignment_2946_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v___x_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2953_, sizeof(void*)*3, v_enabled_2944_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2956_, lean_object* v_trees_2957_, lean_object* v_____r_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_apply_2(v_toPure_2956_, lean_box(0), v_trees_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2960_, lean_object* v_modifyInfoState_2961_, lean_object* v___f_2962_, lean_object* v_toBind_2963_, lean_object* v_____do__lift_2964_){
_start:
{
lean_object* v_trees_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_trees_2965_ = lean_ctor_get(v_____do__lift_2964_, 2);
lean_inc_ref(v_trees_2965_);
lean_dec_ref(v_____do__lift_2964_);
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2966_, 0, v_toPure_2960_);
lean_closure_set(v___f_2966_, 1, v_trees_2965_);
v___x_2967_ = lean_apply_1(v_modifyInfoState_2961_, v___f_2962_);
v___x_2968_ = lean_apply_4(v_toBind_2963_, lean_box(0), lean_box(0), v___x_2967_, v___f_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2970_, lean_object* v_inst_2971_){
_start:
{
lean_object* v_toApplicative_2972_; lean_object* v_toBind_2973_; lean_object* v_getInfoState_2974_; lean_object* v_modifyInfoState_2975_; lean_object* v_toPure_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; 
v_toApplicative_2972_ = lean_ctor_get(v_inst_2970_, 0);
lean_inc_ref(v_toApplicative_2972_);
v_toBind_2973_ = lean_ctor_get(v_inst_2970_, 1);
lean_inc_n(v_toBind_2973_, 2);
lean_dec_ref(v_inst_2970_);
v_getInfoState_2974_ = lean_ctor_get(v_inst_2971_, 0);
lean_inc(v_getInfoState_2974_);
v_modifyInfoState_2975_ = lean_ctor_get(v_inst_2971_, 1);
lean_inc(v_modifyInfoState_2975_);
lean_dec_ref(v_inst_2971_);
v_toPure_2976_ = lean_ctor_get(v_toApplicative_2972_, 1);
lean_inc(v_toPure_2976_);
lean_dec_ref(v_toApplicative_2972_);
v___f_2977_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2978_, 0, v_toPure_2976_);
lean_closure_set(v___f_2978_, 1, v_modifyInfoState_2975_);
lean_closure_set(v___f_2978_, 2, v___f_2977_);
lean_closure_set(v___f_2978_, 3, v_toBind_2973_);
v___x_2979_ = lean_apply_4(v_toBind_2973_, lean_box(0), lean_box(0), v_getInfoState_2974_, v___f_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2981_, v_inst_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2984_, lean_object* v_s_2985_){
_start:
{
uint8_t v_enabled_2986_; lean_object* v_assignment_2987_; lean_object* v_lazyAssignment_2988_; lean_object* v_trees_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2997_; 
v_enabled_2986_ = lean_ctor_get_uint8(v_s_2985_, sizeof(void*)*3);
v_assignment_2987_ = lean_ctor_get(v_s_2985_, 0);
v_lazyAssignment_2988_ = lean_ctor_get(v_s_2985_, 1);
v_trees_2989_ = lean_ctor_get(v_s_2985_, 2);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_s_2985_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2991_ = v_s_2985_;
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_trees_2989_);
lean_inc(v_lazyAssignment_2988_);
lean_inc(v_assignment_2987_);
lean_dec(v_s_2985_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = l_Lean_PersistentArray_push___redArg(v_trees_2989_, v_t_2984_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 2, v___x_2993_);
v___x_2995_ = v___x_2991_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_assignment_2987_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_lazyAssignment_2988_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2996_, sizeof(void*)*3, v_enabled_2986_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2998_, lean_object* v_modifyInfoState_2999_, lean_object* v___f_3000_, lean_object* v_____do__lift_3001_){
_start:
{
uint8_t v_enabled_3002_; 
v_enabled_3002_ = lean_ctor_get_uint8(v_____do__lift_3001_, sizeof(void*)*3);
if (v_enabled_3002_ == 0)
{
lean_object* v_toPure_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec_ref(v___f_3000_);
lean_dec(v_modifyInfoState_2999_);
v_toPure_3003_ = lean_ctor_get(v_toApplicative_2998_, 1);
lean_inc(v_toPure_3003_);
lean_dec_ref(v_toApplicative_2998_);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_apply_2(v_toPure_3003_, lean_box(0), v___x_3004_);
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; 
lean_dec_ref(v_toApplicative_2998_);
v___x_3006_ = lean_apply_1(v_modifyInfoState_2999_, v___f_3000_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_3007_, lean_object* v_modifyInfoState_3008_, lean_object* v___f_3009_, lean_object* v_____do__lift_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_3007_, v_modifyInfoState_3008_, v___f_3009_, v_____do__lift_3010_);
lean_dec_ref(v_____do__lift_3010_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_t_3014_){
_start:
{
lean_object* v_toApplicative_3015_; lean_object* v_toBind_3016_; lean_object* v_getInfoState_3017_; lean_object* v_modifyInfoState_3018_; lean_object* v___f_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; 
v_toApplicative_3015_ = lean_ctor_get(v_inst_3012_, 0);
lean_inc_ref(v_toApplicative_3015_);
v_toBind_3016_ = lean_ctor_get(v_inst_3012_, 1);
lean_inc(v_toBind_3016_);
lean_dec_ref(v_inst_3012_);
v_getInfoState_3017_ = lean_ctor_get(v_inst_3013_, 0);
lean_inc(v_getInfoState_3017_);
v_modifyInfoState_3018_ = lean_ctor_get(v_inst_3013_, 1);
lean_inc(v_modifyInfoState_3018_);
lean_dec_ref(v_inst_3013_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3019_, 0, v_t_3014_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3020_, 0, v_toApplicative_3015_);
lean_closure_set(v___f_3020_, 1, v_modifyInfoState_3018_);
lean_closure_set(v___f_3020_, 2, v___f_3019_);
v___x_3021_ = lean_apply_4(v_toBind_3016_, lean_box(0), lean_box(0), v_getInfoState_3017_, v___f_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_t_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3023_, v_inst_3024_, v_t_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_3027_, lean_object* v_t_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_____do__lift_3031_){
_start:
{
uint8_t v_enabled_3032_; 
v_enabled_3032_ = lean_ctor_get_uint8(v_____do__lift_3031_, sizeof(void*)*3);
if (v_enabled_3032_ == 0)
{
lean_object* v_toPure_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v_inst_3030_);
lean_dec_ref(v_inst_3029_);
lean_dec_ref(v_t_3028_);
v_toPure_3033_ = lean_ctor_get(v_toApplicative_3027_, 1);
lean_inc(v_toPure_3033_);
lean_dec_ref(v_toApplicative_3027_);
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_apply_2(v_toPure_3033_, lean_box(0), v___x_3034_);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec_ref(v_toApplicative_3027_);
v___x_3036_ = lean_unsigned_to_nat(32u);
v___x_3037_ = lean_mk_empty_array_with_capacity(v___x_3036_);
lean_dec_ref(v___x_3037_);
v___x_3038_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_t_3028_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3029_, v_inst_3030_, v___x_3039_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_3041_, lean_object* v_t_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_____do__lift_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_3041_, v_t_3042_, v_inst_3043_, v_inst_3044_, v_____do__lift_3045_);
lean_dec_ref(v_____do__lift_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_t_3049_){
_start:
{
lean_object* v_toApplicative_3050_; lean_object* v_toBind_3051_; lean_object* v_getInfoState_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; 
v_toApplicative_3050_ = lean_ctor_get(v_inst_3047_, 0);
lean_inc_ref(v_toApplicative_3050_);
v_toBind_3051_ = lean_ctor_get(v_inst_3047_, 1);
lean_inc(v_toBind_3051_);
v_getInfoState_3052_ = lean_ctor_get(v_inst_3048_, 0);
lean_inc(v_getInfoState_3052_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3053_, 0, v_toApplicative_3050_);
lean_closure_set(v___f_3053_, 1, v_t_3049_);
lean_closure_set(v___f_3053_, 2, v_inst_3047_);
lean_closure_set(v___f_3053_, 3, v_inst_3048_);
v___x_3054_ = lean_apply_4(v_toBind_3051_, lean_box(0), lean_box(0), v_getInfoState_3052_, v___f_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_t_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3056_, v_inst_3057_, v_t_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_3060_, lean_object* v_inst_3061_, lean_object* v_info_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_info_3062_);
v___x_3064_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3060_, v_inst_3061_, v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_info_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3066_, v_inst_3067_, v_info_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3070_, lean_object* v_expectedType_x3f_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_____do__lift_3074_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_stx_3070_);
v___x_3077_ = l_Lean_LocalContext_empty;
v___x_3078_ = 0;
v___x_3079_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3079_, 0, v___x_3076_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
lean_ctor_set(v___x_3079_, 2, v_expectedType_x3f_3071_);
lean_ctor_set(v___x_3079_, 3, v_____do__lift_3074_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*4, v___x_3078_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*4 + 1, v___x_3078_);
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
v___x_3081_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3072_, v_inst_3073_, v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_stx_3086_, lean_object* v_n_3087_, lean_object* v_expectedType_x3f_3088_){
_start:
{
lean_object* v_toBind_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_toBind_3089_ = lean_ctor_get(v_inst_3082_, 1);
lean_inc(v_toBind_3089_);
lean_inc_ref(v_inst_3082_);
v___f_3090_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3090_, 0, v_stx_3086_);
lean_closure_set(v___f_3090_, 1, v_expectedType_x3f_3088_);
lean_closure_set(v___f_3090_, 2, v_inst_3082_);
lean_closure_set(v___f_3090_, 3, v_inst_3083_);
v___x_3091_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3082_, v_inst_3084_, v_inst_3085_, v_n_3087_);
v___x_3092_ = lean_apply_4(v_toBind_3089_, lean_box(0), lean_box(0), v___x_3091_, v___f_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3093_, lean_object* v_inst_3094_, lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_stx_3098_, lean_object* v_n_3099_, lean_object* v_expectedType_x3f_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3094_, v_inst_3095_, v_inst_3096_, v_inst_3097_, v_stx_3098_, v_n_3099_, v_expectedType_x3f_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v_infoState_3106_; uint8_t v_enabled_3107_; 
v___x_3105_ = lean_st_ref_get(v___y_3103_);
v_infoState_3106_ = lean_ctor_get(v___x_3105_, 7);
lean_inc_ref(v_infoState_3106_);
lean_dec(v___x_3105_);
v_enabled_3107_ = lean_ctor_get_uint8(v_infoState_3106_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3106_);
if (v_enabled_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec_ref(v_t_3102_);
v___x_3108_ = lean_box(0);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v_infoState_3111_; lean_object* v_env_3112_; lean_object* v_nextMacroScope_3113_; lean_object* v_ngen_3114_; lean_object* v_auxDeclNGen_3115_; lean_object* v_traceState_3116_; lean_object* v_cache_3117_; lean_object* v_messages_3118_; lean_object* v_snapshotTasks_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3141_; 
v___x_3110_ = lean_st_ref_take(v___y_3103_);
v_infoState_3111_ = lean_ctor_get(v___x_3110_, 7);
v_env_3112_ = lean_ctor_get(v___x_3110_, 0);
v_nextMacroScope_3113_ = lean_ctor_get(v___x_3110_, 1);
v_ngen_3114_ = lean_ctor_get(v___x_3110_, 2);
v_auxDeclNGen_3115_ = lean_ctor_get(v___x_3110_, 3);
v_traceState_3116_ = lean_ctor_get(v___x_3110_, 4);
v_cache_3117_ = lean_ctor_get(v___x_3110_, 5);
v_messages_3118_ = lean_ctor_get(v___x_3110_, 6);
v_snapshotTasks_3119_ = lean_ctor_get(v___x_3110_, 8);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3141_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_snapshotTasks_3119_);
lean_inc(v_infoState_3111_);
lean_inc(v_messages_3118_);
lean_inc(v_cache_3117_);
lean_inc(v_traceState_3116_);
lean_inc(v_auxDeclNGen_3115_);
lean_inc(v_ngen_3114_);
lean_inc(v_nextMacroScope_3113_);
lean_inc(v_env_3112_);
lean_dec(v___x_3110_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3141_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
uint8_t v_enabled_3123_; lean_object* v_assignment_3124_; lean_object* v_lazyAssignment_3125_; lean_object* v_trees_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3140_; 
v_enabled_3123_ = lean_ctor_get_uint8(v_infoState_3111_, sizeof(void*)*3);
v_assignment_3124_ = lean_ctor_get(v_infoState_3111_, 0);
v_lazyAssignment_3125_ = lean_ctor_get(v_infoState_3111_, 1);
v_trees_3126_ = lean_ctor_get(v_infoState_3111_, 2);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_infoState_3111_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3128_ = v_infoState_3111_;
v_isShared_3129_ = v_isSharedCheck_3140_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_trees_3126_);
lean_inc(v_lazyAssignment_3125_);
lean_inc(v_assignment_3124_);
lean_dec(v_infoState_3111_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3140_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = l_Lean_PersistentArray_push___redArg(v_trees_3126_, v_t_3102_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 2, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_assignment_3124_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_lazyAssignment_3125_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v___x_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*3, v_enabled_3123_);
v___x_3132_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3134_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 7, v___x_3132_);
v___x_3134_ = v___x_3121_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_env_3112_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_nextMacroScope_3113_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_ngen_3114_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_auxDeclNGen_3115_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_traceState_3116_);
lean_ctor_set(v_reuseFailAlloc_3138_, 5, v_cache_3117_);
lean_ctor_set(v_reuseFailAlloc_3138_, 6, v_messages_3118_);
lean_ctor_set(v_reuseFailAlloc_3138_, 7, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3138_, 8, v_snapshotTasks_3119_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_st_ref_set(v___y_3103_, v___x_3134_);
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3142_, v___y_3143_);
lean_dec(v___y_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v_infoState_3151_; uint8_t v_enabled_3152_; 
v___x_3150_ = lean_st_ref_get(v___y_3148_);
v_infoState_3151_ = lean_ctor_get(v___x_3150_, 7);
lean_inc_ref(v_infoState_3151_);
lean_dec(v___x_3150_);
v_enabled_3152_ = lean_ctor_get_uint8(v_infoState_3151_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3151_);
if (v_enabled_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v_t_3146_);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3155_ = lean_unsigned_to_nat(32u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
lean_dec_ref(v___x_3156_);
v___x_3157_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_t_3146_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3158_, v___y_3148_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
lean_ctor_set(v___x_3170_, 3, v___x_3169_);
lean_ctor_set(v___x_3170_, 4, v___x_3168_);
lean_ctor_set(v___x_3170_, 5, v___x_3168_);
lean_ctor_set(v___x_3170_, 6, v___x_3168_);
lean_ctor_set(v___x_3170_, 7, v___x_3168_);
lean_ctor_set(v___x_3170_, 8, v___x_3168_);
lean_ctor_set(v___x_3170_, 9, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3171_ = lean_box(1);
v___x_3172_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
lean_ctor_set(v___x_3174_, 2, v___x_3171_);
return v___x_3174_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3196_, lean_object* v_declHint_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v_env_3201_; uint8_t v___x_3202_; 
v___x_3200_ = lean_st_ref_get(v___y_3198_);
v_env_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc_ref(v_env_3201_);
lean_dec(v___x_3200_);
v___x_3202_ = l_Lean_Name_isAnonymous(v_declHint_3197_);
if (v___x_3202_ == 0)
{
uint8_t v_isExporting_3203_; 
v_isExporting_3203_ = lean_ctor_get_uint8(v_env_3201_, sizeof(void*)*8);
if (v_isExporting_3203_ == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref(v_env_3201_);
lean_dec(v_declHint_3197_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_msg_3196_);
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; uint8_t v___x_3206_; 
lean_inc_ref(v_env_3201_);
v___x_3205_ = l_Lean_Environment_setExporting(v_env_3201_, v___x_3202_);
lean_inc(v_declHint_3197_);
lean_inc_ref(v___x_3205_);
v___x_3206_ = l_Lean_Environment_contains(v___x_3205_, v_declHint_3197_, v_isExporting_3203_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
lean_dec_ref(v___x_3205_);
lean_dec_ref(v_env_3201_);
lean_dec(v_declHint_3197_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_msg_3196_);
return v___x_3207_;
}
else
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_c_3213_; lean_object* v___x_3214_; 
v___x_3208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3209_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3210_ = l_Lean_Options_empty;
v___x_3211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3205_);
lean_ctor_set(v___x_3211_, 1, v___x_3208_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
lean_inc(v_declHint_3197_);
v___x_3212_ = l_Lean_MessageData_ofConstName(v_declHint_3197_, v___x_3202_);
v_c_3213_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3213_, 0, v___x_3211_);
lean_ctor_set(v_c_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3201_, v_declHint_3197_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v_env_3201_);
lean_dec(v_declHint_3197_);
v___x_3215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v_c_3213_);
v___x_3217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = l_Lean_MessageData_note(v___x_3218_);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_msg_3196_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v_val_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3257_; 
v_val_3222_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3224_ = v___x_3214_;
v_isShared_3225_ = v_isSharedCheck_3257_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_val_3222_);
lean_dec(v___x_3214_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3257_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v_mod_3229_; uint8_t v___x_3230_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = l_Lean_Environment_header(v_env_3201_);
lean_dec_ref(v_env_3201_);
v___x_3228_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3227_);
v_mod_3229_ = lean_array_get(v___x_3226_, v___x_3228_, v_val_3222_);
lean_dec(v_val_3222_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = l_Lean_isPrivateName(v_declHint_3197_);
lean_dec(v_declHint_3197_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_c_3213_);
v___x_3233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = l_Lean_MessageData_ofName(v_mod_3229_);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l_Lean_MessageData_note(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_msg_3196_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3240_);
v___x_3242_ = v___x_3224_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v_c_3213_);
v___x_3246_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_MessageData_ofName(v_mod_3229_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_MessageData_note(v___x_3251_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_msg_3196_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3253_);
v___x_3255_ = v___x_3224_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3258_; 
lean_dec_ref(v_env_3201_);
lean_dec(v_declHint_3197_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_msg_3196_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3259_, lean_object* v_declHint_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3259_, v_declHint_3260_, v___y_3261_);
lean_dec(v___y_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3264_, lean_object* v_declHint_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3279_; 
v___x_3269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3264_, v_declHint_3265_, v___y_3267_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3279_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3279_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3274_ = l_Lean_unknownIdentifierMessageTag;
v___x_3275_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v_a_3270_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3275_);
v___x_3277_ = v___x_3272_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3280_, lean_object* v_declHint_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3280_, v_declHint_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v_env_3291_; lean_object* v_options_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3290_ = lean_st_ref_get(v___y_3288_);
v_env_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc_ref(v_env_3291_);
lean_dec(v___x_3290_);
v_options_3292_ = lean_ctor_get(v___y_3287_, 2);
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3294_ = lean_unsigned_to_nat(32u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
lean_dec_ref(v___x_3295_);
v___x_3296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3292_);
v___x_3297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3297_, 0, v_env_3291_);
lean_ctor_set(v___x_3297_, 1, v___x_3293_);
lean_ctor_set(v___x_3297_, 2, v___x_3296_);
lean_ctor_set(v___x_3297_, 3, v_options_3292_);
v___x_3298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v_msgData_3286_);
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_ref_3309_; lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3319_; 
v_ref_3309_ = lean_ctor_get(v___y_3306_, 5);
v___x_3310_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3305_, v___y_3306_, v___y_3307_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3319_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3319_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_inc(v_ref_3309_);
v___x_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3315_, 0, v_ref_3309_);
lean_ctor_set(v___x_3315_, 1, v_a_3311_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 1);
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3325_, lean_object* v_msg_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_fileName_3330_; lean_object* v_fileMap_3331_; lean_object* v_options_3332_; lean_object* v_currRecDepth_3333_; lean_object* v_maxRecDepth_3334_; lean_object* v_ref_3335_; lean_object* v_currNamespace_3336_; lean_object* v_openDecls_3337_; lean_object* v_initHeartbeats_3338_; lean_object* v_maxHeartbeats_3339_; lean_object* v_quotContext_3340_; lean_object* v_currMacroScope_3341_; uint8_t v_diag_3342_; lean_object* v_cancelTk_x3f_3343_; uint8_t v_suppressElabErrors_3344_; lean_object* v_inheritedTraceOptions_3345_; lean_object* v_ref_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_fileName_3330_ = lean_ctor_get(v___y_3327_, 0);
v_fileMap_3331_ = lean_ctor_get(v___y_3327_, 1);
v_options_3332_ = lean_ctor_get(v___y_3327_, 2);
v_currRecDepth_3333_ = lean_ctor_get(v___y_3327_, 3);
v_maxRecDepth_3334_ = lean_ctor_get(v___y_3327_, 4);
v_ref_3335_ = lean_ctor_get(v___y_3327_, 5);
v_currNamespace_3336_ = lean_ctor_get(v___y_3327_, 6);
v_openDecls_3337_ = lean_ctor_get(v___y_3327_, 7);
v_initHeartbeats_3338_ = lean_ctor_get(v___y_3327_, 8);
v_maxHeartbeats_3339_ = lean_ctor_get(v___y_3327_, 9);
v_quotContext_3340_ = lean_ctor_get(v___y_3327_, 10);
v_currMacroScope_3341_ = lean_ctor_get(v___y_3327_, 11);
v_diag_3342_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*14);
v_cancelTk_x3f_3343_ = lean_ctor_get(v___y_3327_, 12);
v_suppressElabErrors_3344_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3345_ = lean_ctor_get(v___y_3327_, 13);
v_ref_3346_ = l_Lean_replaceRef(v_ref_3325_, v_ref_3335_);
lean_inc_ref(v_inheritedTraceOptions_3345_);
lean_inc(v_cancelTk_x3f_3343_);
lean_inc(v_currMacroScope_3341_);
lean_inc(v_quotContext_3340_);
lean_inc(v_maxHeartbeats_3339_);
lean_inc(v_initHeartbeats_3338_);
lean_inc(v_openDecls_3337_);
lean_inc(v_currNamespace_3336_);
lean_inc(v_maxRecDepth_3334_);
lean_inc(v_currRecDepth_3333_);
lean_inc_ref(v_options_3332_);
lean_inc_ref(v_fileMap_3331_);
lean_inc_ref(v_fileName_3330_);
v___x_3347_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3347_, 0, v_fileName_3330_);
lean_ctor_set(v___x_3347_, 1, v_fileMap_3331_);
lean_ctor_set(v___x_3347_, 2, v_options_3332_);
lean_ctor_set(v___x_3347_, 3, v_currRecDepth_3333_);
lean_ctor_set(v___x_3347_, 4, v_maxRecDepth_3334_);
lean_ctor_set(v___x_3347_, 5, v_ref_3346_);
lean_ctor_set(v___x_3347_, 6, v_currNamespace_3336_);
lean_ctor_set(v___x_3347_, 7, v_openDecls_3337_);
lean_ctor_set(v___x_3347_, 8, v_initHeartbeats_3338_);
lean_ctor_set(v___x_3347_, 9, v_maxHeartbeats_3339_);
lean_ctor_set(v___x_3347_, 10, v_quotContext_3340_);
lean_ctor_set(v___x_3347_, 11, v_currMacroScope_3341_);
lean_ctor_set(v___x_3347_, 12, v_cancelTk_x3f_3343_);
lean_ctor_set(v___x_3347_, 13, v_inheritedTraceOptions_3345_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*14, v_diag_3342_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*14 + 1, v_suppressElabErrors_3344_);
v___x_3348_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3326_, v___x_3347_, v___y_3328_);
lean_dec_ref_known(v___x_3347_, 14);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3349_, lean_object* v_msg_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3349_, v_msg_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v_ref_3349_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3355_, lean_object* v_msg_3356_, lean_object* v_declHint_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v_a_3362_; lean_object* v___x_3363_; 
v___x_3361_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3356_, v_declHint_3357_, v___y_3358_, v___y_3359_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3355_, v_a_3362_, v___y_3358_, v___y_3359_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3364_, lean_object* v_msg_3365_, lean_object* v_declHint_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3364_, v_msg_3365_, v_declHint_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v_ref_3364_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3377_, lean_object* v_constName_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3382_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3383_ = 0;
lean_inc(v_constName_3378_);
v___x_3384_ = l_Lean_MessageData_ofConstName(v_constName_3378_, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3382_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3377_, v___x_3387_, v_constName_3378_, v___y_3379_, v___y_3380_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3389_, lean_object* v_constName_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3389_, v_constName_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v_ref_3389_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_ref_3399_; lean_object* v___x_3400_; 
v_ref_3399_ = lean_ctor_get(v___y_3396_, 5);
v___x_3400_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3399_, v_constName_3395_, v___y_3396_, v___y_3397_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; lean_object* v_env_3411_; uint8_t v___x_3412_; lean_object* v___x_3413_; 
v___x_3410_ = lean_st_ref_get(v___y_3408_);
v_env_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc_ref(v_env_3411_);
lean_dec(v___x_3410_);
v___x_3412_ = 0;
lean_inc(v_constName_3406_);
v___x_3413_ = l_Lean_Environment_findConstVal_x3f(v_env_3411_, v_constName_3406_, v___x_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3406_, v___y_3407_, v___y_3408_);
return v___x_3414_;
}
else
{
lean_object* v_val_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_constName_3406_);
v_val_3415_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_val_3415_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set_tag(v___x_3417_, 0);
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_val_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
if (lean_obj_tag(v_a_3428_) == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = l_List_reverse___redArg(v_a_3429_);
return v___x_3430_;
}
else
{
lean_object* v_head_3431_; lean_object* v_tail_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3441_; 
v_head_3431_ = lean_ctor_get(v_a_3428_, 0);
v_tail_3432_ = lean_ctor_get(v_a_3428_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_a_3428_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3434_ = v_a_3428_;
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_tail_3432_);
lean_inc(v_head_3431_);
lean_dec(v_a_3428_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = l_Lean_mkLevelParam(v_head_3431_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v_a_3429_);
lean_ctor_set(v___x_3434_, 0, v___x_3436_);
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_a_3429_);
v___x_3438_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
v_a_3428_ = v_tail_3432_;
v_a_3429_ = v___x_3438_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
lean_inc(v_constName_3442_);
v___x_3446_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3458_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_levelParams_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v_levelParams_3451_ = lean_ctor_get(v_a_3447_, 1);
lean_inc(v_levelParams_3451_);
lean_dec(v_a_3447_);
v___x_3452_ = lean_box(0);
v___x_3453_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3451_, v___x_3452_);
v___x_3454_ = l_Lean_mkConst(v_constName_3442_, v___x_3453_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3454_);
v___x_3456_ = v___x_3449_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_constName_3442_);
v_a_3459_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3446_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3446_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3472_, lean_object* v_n_3473_, lean_object* v_expectedType_x3f_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3473_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = lean_box(0);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v_stx_3472_);
v___x_3482_ = l_Lean_LocalContext_empty;
v___x_3483_ = 0;
v___x_3484_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3484_, 0, v___x_3481_);
lean_ctor_set(v___x_3484_, 1, v___x_3482_);
lean_ctor_set(v___x_3484_, 2, v_expectedType_x3f_3474_);
lean_ctor_set(v___x_3484_, 3, v_a_3479_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*4, v___x_3483_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*4 + 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
v___x_3486_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3485_, v___y_3475_, v___y_3476_);
return v___x_3486_;
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_expectedType_x3f_3474_);
lean_dec(v_stx_3472_);
v_a_3487_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3478_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3478_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3495_, lean_object* v_n_3496_, lean_object* v_expectedType_x3f_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3495_, v_n_3496_, v_expectedType_x3f_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3502_, lean_object* v_expectedType_x3f_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v___x_3507_; 
lean_inc(v_id_3502_);
v___x_3507_ = l_Lean_realizeGlobalConstNoOverload(v_id_3502_, v_a_3504_, v_a_3505_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3535_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3535_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3535_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v_infoState_3513_; uint8_t v_enabled_3514_; 
v___x_3512_ = lean_st_ref_get(v_a_3505_);
v_infoState_3513_ = lean_ctor_get(v___x_3512_, 7);
lean_inc_ref(v_infoState_3513_);
lean_dec(v___x_3512_);
v_enabled_3514_ = lean_ctor_get_uint8(v_infoState_3513_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3513_);
if (v_enabled_3514_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v_expectedType_x3f_3503_);
lean_dec(v_id_3502_);
if (v_isShared_3511_ == 0)
{
v___x_3516_ = v___x_3510_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3508_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
else
{
lean_object* v___x_3518_; 
lean_del_object(v___x_3510_);
lean_inc(v_a_3508_);
v___x_3518_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3502_, v_a_3508_, v_expectedType_x3f_3503_, v_a_3504_, v_a_3505_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v___x_3518_, 0);
lean_dec(v_unused_3526_);
v___x_3520_ = v___x_3518_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_dec(v___x_3518_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_a_3508_);
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3508_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3508_);
v_a_3527_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3518_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3518_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3503_);
lean_dec(v_id_3502_);
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3536_, lean_object* v_expectedType_x3f_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3536_, v_expectedType_x3f_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3542_, v___y_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3552_, lean_object* v_constName_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3553_, v___y_3554_, v___y_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3558_, lean_object* v_constName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3558_, v_constName_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3564_, lean_object* v_ref_3565_, lean_object* v_constName_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3565_, v_constName_3566_, v___y_3567_, v___y_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3571_, lean_object* v_ref_3572_, lean_object* v_constName_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3571_, v_ref_3572_, v_constName_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v_ref_3572_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3578_, lean_object* v_ref_3579_, lean_object* v_msg_3580_, lean_object* v_declHint_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3579_, v_msg_3580_, v_declHint_3581_, v___y_3582_, v___y_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3586_, lean_object* v_ref_3587_, lean_object* v_msg_3588_, lean_object* v_declHint_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3586_, v_ref_3587_, v_msg_3588_, v_declHint_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v_ref_3587_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3594_, lean_object* v_declHint_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3594_, v_declHint_3595_, v___y_3597_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3600_, lean_object* v_declHint_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3600_, v_declHint_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3606_, lean_object* v_ref_3607_, lean_object* v_msg_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3607_, v_msg_3608_, v___y_3609_, v___y_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_ref_3614_, lean_object* v_msg_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3613_, v_ref_3614_, v_msg_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v_ref_3614_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3621_, v___y_3622_, v___y_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3626_, lean_object* v_msg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3626_, v_msg_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3632_, lean_object* v_expectedType_x3f_3633_, lean_object* v_as_x27_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
if (lean_obj_tag(v_as_x27_3634_) == 0)
{
lean_object* v___x_3639_; 
lean_dec(v_expectedType_x3f_3633_);
lean_dec(v_id_3632_);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_b_3635_);
return v___x_3639_;
}
else
{
lean_object* v_head_3640_; lean_object* v_tail_3641_; lean_object* v___x_3642_; 
v_head_3640_ = lean_ctor_get(v_as_x27_3634_, 0);
v_tail_3641_ = lean_ctor_get(v_as_x27_3634_, 1);
lean_inc(v_expectedType_x3f_3633_);
lean_inc(v_head_3640_);
lean_inc(v_id_3632_);
v___x_3642_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3632_, v_head_3640_, v_expectedType_x3f_3633_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v___x_3643_; 
lean_dec_ref_known(v___x_3642_, 1);
v___x_3643_ = lean_box(0);
v_as_x27_3634_ = v_tail_3641_;
v_b_3635_ = v___x_3643_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_3633_);
lean_dec(v_id_3632_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3645_, lean_object* v_expectedType_x3f_3646_, lean_object* v_as_x27_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3645_, v_expectedType_x3f_3646_, v_as_x27_3647_, v_b_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v_as_x27_3647_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3653_, lean_object* v_expectedType_x3f_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; 
lean_inc(v_id_3653_);
v___x_3658_ = l_Lean_realizeGlobalConst(v_id_3653_, v_a_3655_, v_a_3656_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3687_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3687_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3687_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v_infoState_3664_; uint8_t v_enabled_3665_; 
v___x_3663_ = lean_st_ref_get(v_a_3656_);
v_infoState_3664_ = lean_ctor_get(v___x_3663_, 7);
lean_inc_ref(v_infoState_3664_);
lean_dec(v___x_3663_);
v_enabled_3665_ = lean_ctor_get_uint8(v_infoState_3664_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3664_);
if (v_enabled_3665_ == 0)
{
lean_object* v___x_3667_; 
lean_dec(v_expectedType_x3f_3654_);
lean_dec(v_id_3653_);
if (v_isShared_3662_ == 0)
{
v___x_3667_ = v___x_3661_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3659_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_del_object(v___x_3661_);
v___x_3669_ = lean_box(0);
v___x_3670_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3653_, v_expectedType_x3f_3654_, v_a_3659_, v___x_3669_, v_a_3655_, v_a_3656_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v___x_3670_, 0);
lean_dec(v_unused_3678_);
v___x_3672_ = v___x_3670_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v___x_3670_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_a_3659_);
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3659_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_a_3659_);
v_a_3679_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3654_);
lean_dec(v_id_3653_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3688_, lean_object* v_expectedType_x3f_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3688_, v_expectedType_x3f_3689_, v_a_3690_, v_a_3691_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3694_, lean_object* v_expectedType_x3f_3695_, lean_object* v_as_3696_, lean_object* v_as_x27_3697_, lean_object* v_b_3698_, lean_object* v_a_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3694_, v_expectedType_x3f_3695_, v_as_x27_3697_, v_b_3698_, v___y_3700_, v___y_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3704_, lean_object* v_expectedType_x3f_3705_, lean_object* v_as_3706_, lean_object* v_as_x27_3707_, lean_object* v_b_3708_, lean_object* v_a_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3704_, v_expectedType_x3f_3705_, v_as_3706_, v_as_x27_3707_, v_b_3708_, v_a_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v_as_x27_3707_);
lean_dec(v_as_3706_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3714_, lean_object* v_as_x27_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
if (lean_obj_tag(v_as_x27_3715_) == 0)
{
lean_object* v___x_3720_; 
lean_dec(v_ref_3714_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_b_3716_);
return v___x_3720_;
}
else
{
lean_object* v_head_3721_; lean_object* v_tail_3722_; lean_object* v_fst_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_head_3721_ = lean_ctor_get(v_as_x27_3715_, 0);
v_tail_3722_ = lean_ctor_get(v_as_x27_3715_, 1);
v_fst_3723_ = lean_ctor_get(v_head_3721_, 0);
v___x_3724_ = lean_box(0);
lean_inc(v_fst_3723_);
lean_inc(v_ref_3714_);
v___x_3725_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3714_, v_fst_3723_, v___x_3724_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3726_; 
lean_dec_ref_known(v___x_3725_, 1);
v___x_3726_ = lean_box(0);
v_as_x27_3715_ = v_tail_3722_;
v_b_3716_ = v___x_3726_;
goto _start;
}
else
{
lean_dec(v_ref_3714_);
return v___x_3725_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3728_, lean_object* v_as_x27_3729_, lean_object* v_b_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3728_, v_as_x27_3729_, v_b_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v_as_x27_3729_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3735_, lean_object* v_id_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_realizeGlobalName(v_id_3736_, v_a_3737_, v_a_3738_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3769_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3769_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3769_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v_infoState_3746_; uint8_t v_enabled_3747_; 
v___x_3745_ = lean_st_ref_get(v_a_3738_);
v_infoState_3746_ = lean_ctor_get(v___x_3745_, 7);
lean_inc_ref(v_infoState_3746_);
lean_dec(v___x_3745_);
v_enabled_3747_ = lean_ctor_get_uint8(v_infoState_3746_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3746_);
if (v_enabled_3747_ == 0)
{
lean_object* v___x_3749_; 
lean_dec(v_ref_3735_);
if (v_isShared_3744_ == 0)
{
v___x_3749_ = v___x_3743_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3741_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_del_object(v___x_3743_);
v___x_3751_ = lean_box(0);
v___x_3752_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3735_, v_a_3741_, v___x_3751_, v_a_3737_, v_a_3738_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v___x_3752_, 0);
lean_dec(v_unused_3760_);
v___x_3754_ = v___x_3752_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_dec(v___x_3752_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v_a_3741_);
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3741_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3741_);
v_a_3761_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3752_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3752_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_3735_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3770_, lean_object* v_id_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3770_, v_id_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3776_, lean_object* v_as_3777_, lean_object* v_as_x27_3778_, lean_object* v_b_3779_, lean_object* v_a_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3776_, v_as_x27_3778_, v_b_3779_, v___y_3781_, v___y_3782_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3785_, lean_object* v_as_3786_, lean_object* v_as_x27_3787_, lean_object* v_b_3788_, lean_object* v_a_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3785_, v_as_3786_, v_as_x27_3787_, v_b_3788_, v_a_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v_as_x27_3787_);
lean_dec(v_as_3786_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3794_){
_start:
{
lean_object* v_fst_3795_; 
v_fst_3795_ = lean_ctor_get(v_self_3794_, 0);
lean_inc(v_fst_3795_);
return v_fst_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3796_);
lean_dec_ref(v_self_3796_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3798_, lean_object* v_treesSaved_3799_, lean_object* v_s_3800_){
_start:
{
if (lean_obj_tag(v_info_3798_) == 0)
{
uint8_t v_enabled_3801_; lean_object* v_assignment_3802_; lean_object* v_lazyAssignment_3803_; lean_object* v_trees_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3814_; 
v_enabled_3801_ = lean_ctor_get_uint8(v_s_3800_, sizeof(void*)*3);
v_assignment_3802_ = lean_ctor_get(v_s_3800_, 0);
v_lazyAssignment_3803_ = lean_ctor_get(v_s_3800_, 1);
v_trees_3804_ = lean_ctor_get(v_s_3800_, 2);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_s_3800_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3806_ = v_s_3800_;
v_isShared_3807_ = v_isSharedCheck_3814_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_trees_3804_);
lean_inc(v_lazyAssignment_3803_);
lean_inc(v_assignment_3802_);
lean_dec(v_s_3800_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3814_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v_val_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v_val_3808_ = lean_ctor_get(v_info_3798_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v_info_3798_, 1);
v___x_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_val_3808_);
lean_ctor_set(v___x_3809_, 1, v_trees_3804_);
v___x_3810_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3799_, v___x_3809_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 2, v___x_3810_);
v___x_3812_ = v___x_3806_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_assignment_3802_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_lazyAssignment_3803_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v___x_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*3, v_enabled_3801_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
uint8_t v_enabled_3815_; lean_object* v_assignment_3816_; lean_object* v_lazyAssignment_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3833_; 
v_enabled_3815_ = lean_ctor_get_uint8(v_s_3800_, sizeof(void*)*3);
v_assignment_3816_ = lean_ctor_get(v_s_3800_, 0);
v_lazyAssignment_3817_ = lean_ctor_get(v_s_3800_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_s_3800_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v_s_3800_, 2);
lean_dec(v_unused_3834_);
v___x_3819_ = v_s_3800_;
v_isShared_3820_ = v_isSharedCheck_3833_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_lazyAssignment_3817_);
lean_inc(v_assignment_3816_);
lean_dec(v_s_3800_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3833_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v_val_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3832_; 
v_val_3821_ = lean_ctor_get(v_info_3798_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_info_3798_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3823_ = v_info_3798_;
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_val_3821_);
lean_dec(v_info_3798_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set_tag(v___x_3823_, 2);
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_val_3821_);
v___x_3826_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3799_, v___x_3826_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 2, v___x_3827_);
v___x_3829_ = v___x_3819_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_assignment_3816_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_lazyAssignment_3817_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v___x_3827_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*3, v_enabled_3815_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3835_, lean_object* v_modifyInfoState_3836_, lean_object* v_info_3837_){
_start:
{
lean_object* v___f_3838_; lean_object* v___x_3839_; 
v___f_3838_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3838_, 0, v_info_3837_);
lean_closure_set(v___f_3838_, 1, v_treesSaved_3835_);
v___x_3839_ = lean_apply_1(v_modifyInfoState_3836_, v___f_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3840_, lean_object* v_info_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_apply_1(v___f_3840_, v_info_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3843_, lean_object* v_toBind_3844_, lean_object* v___f_3845_, lean_object* v_____do__lift_3846_){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_____do__lift_3846_);
v___x_3848_ = lean_apply_2(v_toPure_3843_, lean_box(0), v___x_3847_);
v___x_3849_ = lean_apply_4(v_toBind_3844_, lean_box(0), lean_box(0), v___x_3848_, v___f_3845_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3850_, lean_object* v_mkInfoOnError_3851_, lean_object* v___f_3852_, lean_object* v_mkInfo_3853_, lean_object* v___f_3854_, lean_object* v_a_x3f_3855_){
_start:
{
if (lean_obj_tag(v_a_x3f_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec(v___f_3854_);
lean_dec(v_mkInfo_3853_);
v___x_3856_ = lean_apply_4(v_toBind_3850_, lean_box(0), lean_box(0), v_mkInfoOnError_3851_, v___f_3852_);
return v___x_3856_;
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec(v___f_3852_);
lean_dec(v_mkInfoOnError_3851_);
v_val_3857_ = lean_ctor_get(v_a_x3f_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_a_x3f_3855_, 1);
v___x_3858_ = lean_apply_1(v_mkInfo_3853_, v_val_3857_);
v___x_3859_ = lean_apply_4(v_toBind_3850_, lean_box(0), lean_box(0), v___x_3858_, v___f_3854_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3860_, lean_object* v_modifyInfoState_3861_, lean_object* v_toBind_3862_, lean_object* v_mkInfoOnError_3863_, lean_object* v_mkInfo_3864_, lean_object* v_inst_3865_, lean_object* v_x_3866_, lean_object* v___f_3867_, lean_object* v_treesSaved_3868_){
_start:
{
lean_object* v_toFunctor_3869_; lean_object* v_toPure_3870_; lean_object* v_map_3871_; lean_object* v___f_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; lean_object* v___f_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_toFunctor_3869_ = lean_ctor_get(v_toApplicative_3860_, 0);
lean_inc_ref(v_toFunctor_3869_);
v_toPure_3870_ = lean_ctor_get(v_toApplicative_3860_, 1);
lean_inc(v_toPure_3870_);
lean_dec_ref(v_toApplicative_3860_);
v_map_3871_ = lean_ctor_get(v_toFunctor_3869_, 0);
lean_inc(v_map_3871_);
lean_dec_ref(v_toFunctor_3869_);
v___f_3872_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3872_, 0, v_treesSaved_3868_);
lean_closure_set(v___f_3872_, 1, v_modifyInfoState_3861_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3873_, 0, v___f_3872_);
lean_inc_ref(v___f_3873_);
lean_inc(v_toBind_3862_);
v___f_3874_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3874_, 0, v_toPure_3870_);
lean_closure_set(v___f_3874_, 1, v_toBind_3862_);
lean_closure_set(v___f_3874_, 2, v___f_3873_);
v___f_3875_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3875_, 0, v_toBind_3862_);
lean_closure_set(v___f_3875_, 1, v_mkInfoOnError_3863_);
lean_closure_set(v___f_3875_, 2, v___f_3874_);
lean_closure_set(v___f_3875_, 3, v_mkInfo_3864_);
lean_closure_set(v___f_3875_, 4, v___f_3873_);
v___x_3876_ = lean_apply_4(v_inst_3865_, lean_box(0), lean_box(0), v_x_3866_, v___f_3875_);
v___x_3877_ = lean_apply_4(v_map_3871_, lean_box(0), lean_box(0), v___f_3867_, v___x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3878_, lean_object* v_inst_3879_, lean_object* v_inst_3880_, lean_object* v_toBind_3881_, lean_object* v___f_3882_, lean_object* v_____do__lift_3883_){
_start:
{
uint8_t v_enabled_3884_; 
v_enabled_3884_ = lean_ctor_get_uint8(v_____do__lift_3883_, sizeof(void*)*3);
if (v_enabled_3884_ == 0)
{
lean_dec(v___f_3882_);
lean_dec(v_toBind_3881_);
lean_dec_ref(v_inst_3880_);
lean_dec_ref(v_inst_3879_);
lean_inc(v_x_3878_);
return v_x_3878_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3879_, v_inst_3880_);
v___x_3886_ = lean_apply_4(v_toBind_3881_, lean_box(0), lean_box(0), v___x_3885_, v___f_3882_);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3887_, lean_object* v_inst_3888_, lean_object* v_inst_3889_, lean_object* v_toBind_3890_, lean_object* v___f_3891_, lean_object* v_____do__lift_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3887_, v_inst_3888_, v_inst_3889_, v_toBind_3890_, v___f_3891_, v_____do__lift_3892_);
lean_dec_ref(v_____do__lift_3892_);
lean_dec(v_x_3887_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_inst_3897_, lean_object* v_x_3898_, lean_object* v_mkInfo_3899_, lean_object* v_mkInfoOnError_3900_){
_start:
{
lean_object* v_toApplicative_3901_; lean_object* v_toBind_3902_; lean_object* v_getInfoState_3903_; lean_object* v_modifyInfoState_3904_; lean_object* v___f_3905_; lean_object* v___f_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; 
v_toApplicative_3901_ = lean_ctor_get(v_inst_3895_, 0);
v_toBind_3902_ = lean_ctor_get(v_inst_3895_, 1);
lean_inc_n(v_toBind_3902_, 3);
v_getInfoState_3903_ = lean_ctor_get(v_inst_3896_, 0);
lean_inc(v_getInfoState_3903_);
v_modifyInfoState_3904_ = lean_ctor_get(v_inst_3896_, 1);
v___f_3905_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3898_);
lean_inc(v_modifyInfoState_3904_);
lean_inc_ref(v_toApplicative_3901_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3906_, 0, v_toApplicative_3901_);
lean_closure_set(v___f_3906_, 1, v_modifyInfoState_3904_);
lean_closure_set(v___f_3906_, 2, v_toBind_3902_);
lean_closure_set(v___f_3906_, 3, v_mkInfoOnError_3900_);
lean_closure_set(v___f_3906_, 4, v_mkInfo_3899_);
lean_closure_set(v___f_3906_, 5, v_inst_3897_);
lean_closure_set(v___f_3906_, 6, v_x_3898_);
lean_closure_set(v___f_3906_, 7, v___f_3905_);
v___f_3907_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3907_, 0, v_x_3898_);
lean_closure_set(v___f_3907_, 1, v_inst_3895_);
lean_closure_set(v___f_3907_, 2, v_inst_3896_);
lean_closure_set(v___f_3907_, 3, v_toBind_3902_);
lean_closure_set(v___f_3907_, 4, v___f_3906_);
v___x_3908_ = lean_apply_4(v_toBind_3902_, lean_box(0), lean_box(0), v_getInfoState_3903_, v___f_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3909_, lean_object* v_inst_3910_, lean_object* v_inst_3911_, lean_object* v_00_u03b1_3912_, lean_object* v_inst_3913_, lean_object* v_x_3914_, lean_object* v_mkInfo_3915_, lean_object* v_mkInfoOnError_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3910_, v_inst_3911_, v_inst_3913_, v_x_3914_, v_mkInfo_3915_, v_mkInfoOnError_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3918_, lean_object* v_tree_3919_, lean_object* v_s_3920_){
_start:
{
uint8_t v_enabled_3921_; lean_object* v_assignment_3922_; lean_object* v_lazyAssignment_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
v_enabled_3921_ = lean_ctor_get_uint8(v_s_3920_, sizeof(void*)*3);
v_assignment_3922_ = lean_ctor_get(v_s_3920_, 0);
v_lazyAssignment_3923_ = lean_ctor_get(v_s_3920_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_s_3920_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_s_3920_, 2);
lean_dec(v_unused_3932_);
v___x_3925_ = v_s_3920_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_lazyAssignment_3923_);
lean_inc(v_assignment_3922_);
lean_dec(v_s_3920_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3918_, v_tree_3919_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 2, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_assignment_3922_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_lazyAssignment_3923_);
lean_ctor_set(v_reuseFailAlloc_3930_, 2, v___x_3927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3930_, sizeof(void*)*3, v_enabled_3921_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3933_, lean_object* v_modifyInfoState_3934_, lean_object* v_tree_3935_){
_start:
{
lean_object* v___f_3936_; lean_object* v___x_3937_; 
v___f_3936_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3936_, 0, v_treesSaved_3933_);
lean_closure_set(v___f_3936_, 1, v_tree_3935_);
v___x_3937_ = lean_apply_1(v_modifyInfoState_3934_, v___f_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3938_, lean_object* v_toBind_3939_, lean_object* v___f_3940_, lean_object* v_st_3941_){
_start:
{
lean_object* v_trees_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_trees_3942_ = lean_ctor_get(v_st_3941_, 2);
lean_inc_ref(v_trees_3942_);
lean_dec_ref(v_st_3941_);
v___x_3943_ = lean_apply_1(v_mkInfoTree_3938_, v_trees_3942_);
v___x_3944_ = lean_apply_4(v_toBind_3939_, lean_box(0), lean_box(0), v___x_3943_, v___f_3940_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3945_, lean_object* v_getInfoState_3946_, lean_object* v___f_3947_, lean_object* v_x_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_apply_4(v_toBind_3945_, lean_box(0), lean_box(0), v_getInfoState_3946_, v___f_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3950_, lean_object* v_getInfoState_3951_, lean_object* v___f_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3950_, v_getInfoState_3951_, v___f_3952_, v_x_3953_);
lean_dec(v_x_3953_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3955_, lean_object* v_modifyInfoState_3956_, lean_object* v_mkInfoTree_3957_, lean_object* v_toBind_3958_, lean_object* v_getInfoState_3959_, lean_object* v_inst_3960_, lean_object* v_x_3961_, lean_object* v___f_3962_, lean_object* v_treesSaved_3963_){
_start:
{
lean_object* v_toFunctor_3964_; lean_object* v_map_3965_; lean_object* v___f_3966_; lean_object* v___f_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_toFunctor_3964_ = lean_ctor_get(v_toApplicative_3955_, 0);
lean_inc_ref(v_toFunctor_3964_);
lean_dec_ref(v_toApplicative_3955_);
v_map_3965_ = lean_ctor_get(v_toFunctor_3964_, 0);
lean_inc(v_map_3965_);
lean_dec_ref(v_toFunctor_3964_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3966_, 0, v_treesSaved_3963_);
lean_closure_set(v___f_3966_, 1, v_modifyInfoState_3956_);
lean_inc(v_toBind_3958_);
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3967_, 0, v_mkInfoTree_3957_);
lean_closure_set(v___f_3967_, 1, v_toBind_3958_);
lean_closure_set(v___f_3967_, 2, v___f_3966_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3968_, 0, v_toBind_3958_);
lean_closure_set(v___f_3968_, 1, v_getInfoState_3959_);
lean_closure_set(v___f_3968_, 2, v___f_3967_);
v___x_3969_ = lean_apply_4(v_inst_3960_, lean_box(0), lean_box(0), v_x_3961_, v___f_3968_);
v___x_3970_ = lean_apply_4(v_map_3965_, lean_box(0), lean_box(0), v___f_3962_, v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_x_3974_, lean_object* v_mkInfoTree_3975_){
_start:
{
lean_object* v_toApplicative_3976_; lean_object* v_toBind_3977_; lean_object* v_getInfoState_3978_; lean_object* v_modifyInfoState_3979_; lean_object* v___f_3980_; lean_object* v___f_3981_; lean_object* v___f_3982_; lean_object* v___x_3983_; 
v_toApplicative_3976_ = lean_ctor_get(v_inst_3971_, 0);
v_toBind_3977_ = lean_ctor_get(v_inst_3971_, 1);
lean_inc_n(v_toBind_3977_, 3);
v_getInfoState_3978_ = lean_ctor_get(v_inst_3972_, 0);
lean_inc_n(v_getInfoState_3978_, 2);
v_modifyInfoState_3979_ = lean_ctor_get(v_inst_3972_, 1);
v___f_3980_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3974_);
lean_inc(v_modifyInfoState_3979_);
lean_inc_ref(v_toApplicative_3976_);
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3981_, 0, v_toApplicative_3976_);
lean_closure_set(v___f_3981_, 1, v_modifyInfoState_3979_);
lean_closure_set(v___f_3981_, 2, v_mkInfoTree_3975_);
lean_closure_set(v___f_3981_, 3, v_toBind_3977_);
lean_closure_set(v___f_3981_, 4, v_getInfoState_3978_);
lean_closure_set(v___f_3981_, 5, v_inst_3973_);
lean_closure_set(v___f_3981_, 6, v_x_3974_);
lean_closure_set(v___f_3981_, 7, v___f_3980_);
v___f_3982_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3982_, 0, v_x_3974_);
lean_closure_set(v___f_3982_, 1, v_inst_3971_);
lean_closure_set(v___f_3982_, 2, v_inst_3972_);
lean_closure_set(v___f_3982_, 3, v_toBind_3977_);
lean_closure_set(v___f_3982_, 4, v___f_3981_);
v___x_3983_ = lean_apply_4(v_toBind_3977_, lean_box(0), lean_box(0), v_getInfoState_3978_, v___f_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3984_, lean_object* v_inst_3985_, lean_object* v_inst_3986_, lean_object* v_00_u03b1_3987_, lean_object* v_inst_3988_, lean_object* v_x_3989_, lean_object* v_mkInfoTree_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3985_, v_inst_3986_, v_inst_3988_, v_x_3989_, v_mkInfoTree_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3992_, lean_object* v_toPure_3993_, lean_object* v_____do__lift_3994_){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v_____do__lift_3994_);
lean_ctor_set(v___x_3995_, 1, v_trees_3992_);
v___x_3996_ = lean_apply_2(v_toPure_3993_, lean_box(0), v___x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3997_, lean_object* v_toBind_3998_, lean_object* v_mkInfo_3999_, lean_object* v_trees_4000_){
_start:
{
lean_object* v___f_4001_; lean_object* v___x_4002_; 
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4001_, 0, v_trees_4000_);
lean_closure_set(v___f_4001_, 1, v_toPure_3997_);
v___x_4002_ = lean_apply_4(v_toBind_3998_, lean_box(0), lean_box(0), v_mkInfo_3999_, v___f_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_inst_4005_, lean_object* v_x_4006_, lean_object* v_mkInfo_4007_){
_start:
{
lean_object* v_toApplicative_4008_; lean_object* v_toBind_4009_; lean_object* v_toPure_4010_; lean_object* v___f_4011_; lean_object* v___x_4012_; 
v_toApplicative_4008_ = lean_ctor_get(v_inst_4003_, 0);
v_toBind_4009_ = lean_ctor_get(v_inst_4003_, 1);
v_toPure_4010_ = lean_ctor_get(v_toApplicative_4008_, 1);
lean_inc(v_toBind_4009_);
lean_inc(v_toPure_4010_);
v___f_4011_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4011_, 0, v_toPure_4010_);
lean_closure_set(v___f_4011_, 1, v_toBind_4009_);
lean_closure_set(v___f_4011_, 2, v_mkInfo_4007_);
v___x_4012_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4003_, v_inst_4004_, v_inst_4005_, v_x_4006_, v___f_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_4013_, lean_object* v_inst_4014_, lean_object* v_inst_4015_, lean_object* v_00_u03b1_4016_, lean_object* v_inst_4017_, lean_object* v_x_4018_, lean_object* v_mkInfo_4019_){
_start:
{
lean_object* v_toApplicative_4020_; lean_object* v_toBind_4021_; lean_object* v_toPure_4022_; lean_object* v___f_4023_; lean_object* v___x_4024_; 
v_toApplicative_4020_ = lean_ctor_get(v_inst_4014_, 0);
v_toBind_4021_ = lean_ctor_get(v_inst_4014_, 1);
v_toPure_4022_ = lean_ctor_get(v_toApplicative_4020_, 1);
lean_inc(v_toBind_4021_);
lean_inc(v_toPure_4022_);
v___f_4023_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4023_, 0, v_toPure_4022_);
lean_closure_set(v___f_4023_, 1, v_toBind_4021_);
lean_closure_set(v___f_4023_, 2, v_mkInfo_4019_);
v___x_4024_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4014_, v_inst_4015_, v_inst_4017_, v_x_4018_, v___f_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_4025_, lean_object* v_trees_4026_, lean_object* v_s_4027_){
_start:
{
uint8_t v_enabled_4028_; lean_object* v_assignment_4029_; lean_object* v_lazyAssignment_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4038_; 
v_enabled_4028_ = lean_ctor_get_uint8(v_s_4027_, sizeof(void*)*3);
v_assignment_4029_ = lean_ctor_get(v_s_4027_, 0);
v_lazyAssignment_4030_ = lean_ctor_get(v_s_4027_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_s_4027_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; 
v_unused_4039_ = lean_ctor_get(v_s_4027_, 2);
lean_dec(v_unused_4039_);
v___x_4032_ = v_s_4027_;
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_lazyAssignment_4030_);
lean_inc(v_assignment_4029_);
lean_dec(v_s_4027_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4034_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_4025_, v_trees_4026_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 2, v___x_4034_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_assignment_4029_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_lazyAssignment_4030_);
lean_ctor_set(v_reuseFailAlloc_4037_, 2, v___x_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4037_, sizeof(void*)*3, v_enabled_4028_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_4040_, lean_object* v_trees_4041_, lean_object* v_s_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_4040_, v_trees_4041_, v_s_4042_);
lean_dec_ref(v_trees_4041_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_4044_, lean_object* v_modifyInfoState_4045_, lean_object* v_trees_4046_){
_start:
{
lean_object* v___f_4047_; lean_object* v___x_4048_; 
v___f_4047_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4047_, 0, v_treesSaved_4044_);
lean_closure_set(v___f_4047_, 1, v_trees_4046_);
v___x_4048_ = lean_apply_1(v_modifyInfoState_4045_, v___f_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_4049_, lean_object* v_tree_4050_, lean_object* v_____do__lift_4051_){
_start:
{
if (lean_obj_tag(v_____do__lift_4051_) == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_apply_2(v_toPure_4049_, lean_box(0), v_tree_4050_);
return v___x_4052_;
}
else
{
lean_object* v_val_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_val_4053_ = lean_ctor_get(v_____do__lift_4051_, 0);
lean_inc(v_val_4053_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v_val_4053_);
lean_ctor_set(v___x_4054_, 1, v_tree_4050_);
v___x_4055_ = lean_apply_2(v_toPure_4049_, lean_box(0), v___x_4054_);
return v___x_4055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_4056_, lean_object* v_tree_4057_, lean_object* v_____do__lift_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_4056_, v_tree_4057_, v_____do__lift_4058_);
lean_dec(v_____do__lift_4058_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4060_, lean_object* v_toPure_4061_, lean_object* v_toBind_4062_, lean_object* v_ctx_x3f_4063_, lean_object* v_tree_4064_){
_start:
{
lean_object* v_tree_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; 
v_tree_4065_ = l_Lean_Elab_InfoTree_substitute(v_tree_4064_, v_assignment_4060_);
v___f_4066_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4066_, 0, v_toPure_4061_);
lean_closure_set(v___f_4066_, 1, v_tree_4065_);
v___x_4067_ = lean_apply_4(v_toBind_4062_, lean_box(0), lean_box(0), v_ctx_x3f_4063_, v___f_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_4068_, lean_object* v_toPure_4069_, lean_object* v_toBind_4070_, lean_object* v_ctx_x3f_4071_, lean_object* v_tree_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_4068_, v_toPure_4069_, v_toBind_4070_, v_ctx_x3f_4071_, v_tree_4072_);
lean_dec_ref(v_assignment_4068_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4074_, lean_object* v_toBind_4075_, lean_object* v_ctx_x3f_4076_, lean_object* v_inst_4077_, lean_object* v___f_4078_, lean_object* v_st_4079_){
_start:
{
lean_object* v_assignment_4080_; lean_object* v_trees_4081_; lean_object* v___f_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v_assignment_4080_ = lean_ctor_get(v_st_4079_, 0);
lean_inc_ref(v_assignment_4080_);
v_trees_4081_ = lean_ctor_get(v_st_4079_, 2);
lean_inc_ref(v_trees_4081_);
lean_dec_ref(v_st_4079_);
lean_inc(v_toBind_4075_);
v___f_4082_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4082_, 0, v_assignment_4080_);
lean_closure_set(v___f_4082_, 1, v_toPure_4074_);
lean_closure_set(v___f_4082_, 2, v_toBind_4075_);
lean_closure_set(v___f_4082_, 3, v_ctx_x3f_4076_);
v___x_4083_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4077_, v___f_4082_, v_trees_4081_);
v___x_4084_ = lean_apply_4(v_toBind_4075_, lean_box(0), lean_box(0), v___x_4083_, v___f_4078_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4085_, lean_object* v_modifyInfoState_4086_, lean_object* v_toBind_4087_, lean_object* v_ctx_x3f_4088_, lean_object* v_inst_4089_, lean_object* v_getInfoState_4090_, lean_object* v_inst_4091_, lean_object* v_x_4092_, lean_object* v___f_4093_, lean_object* v_treesSaved_4094_){
_start:
{
lean_object* v_toFunctor_4095_; lean_object* v_toPure_4096_; lean_object* v_map_4097_; lean_object* v___f_4098_; lean_object* v___f_4099_; lean_object* v___f_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_toFunctor_4095_ = lean_ctor_get(v_toApplicative_4085_, 0);
lean_inc_ref(v_toFunctor_4095_);
v_toPure_4096_ = lean_ctor_get(v_toApplicative_4085_, 1);
lean_inc(v_toPure_4096_);
lean_dec_ref(v_toApplicative_4085_);
v_map_4097_ = lean_ctor_get(v_toFunctor_4095_, 0);
lean_inc(v_map_4097_);
lean_dec_ref(v_toFunctor_4095_);
v___f_4098_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4098_, 0, v_treesSaved_4094_);
lean_closure_set(v___f_4098_, 1, v_modifyInfoState_4086_);
lean_inc(v_toBind_4087_);
v___f_4099_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4099_, 0, v_toPure_4096_);
lean_closure_set(v___f_4099_, 1, v_toBind_4087_);
lean_closure_set(v___f_4099_, 2, v_ctx_x3f_4088_);
lean_closure_set(v___f_4099_, 3, v_inst_4089_);
lean_closure_set(v___f_4099_, 4, v___f_4098_);
v___f_4100_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4100_, 0, v_toBind_4087_);
lean_closure_set(v___f_4100_, 1, v_getInfoState_4090_);
lean_closure_set(v___f_4100_, 2, v___f_4099_);
v___x_4101_ = lean_apply_4(v_inst_4091_, lean_box(0), lean_box(0), v_x_4092_, v___f_4100_);
v___x_4102_ = lean_apply_4(v_map_4097_, lean_box(0), lean_box(0), v___f_4093_, v___x_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4103_, lean_object* v_inst_4104_, lean_object* v_inst_4105_, lean_object* v_x_4106_, lean_object* v_ctx_x3f_4107_){
_start:
{
lean_object* v_toApplicative_4108_; lean_object* v_toBind_4109_; lean_object* v_getInfoState_4110_; lean_object* v_modifyInfoState_4111_; lean_object* v___f_4112_; lean_object* v___f_4113_; lean_object* v___f_4114_; lean_object* v___x_4115_; 
v_toApplicative_4108_ = lean_ctor_get(v_inst_4103_, 0);
v_toBind_4109_ = lean_ctor_get(v_inst_4103_, 1);
lean_inc_n(v_toBind_4109_, 3);
v_getInfoState_4110_ = lean_ctor_get(v_inst_4104_, 0);
lean_inc_n(v_getInfoState_4110_, 2);
v_modifyInfoState_4111_ = lean_ctor_get(v_inst_4104_, 1);
v___f_4112_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4106_);
lean_inc_ref(v_inst_4103_);
lean_inc(v_modifyInfoState_4111_);
lean_inc_ref(v_toApplicative_4108_);
v___f_4113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4113_, 0, v_toApplicative_4108_);
lean_closure_set(v___f_4113_, 1, v_modifyInfoState_4111_);
lean_closure_set(v___f_4113_, 2, v_toBind_4109_);
lean_closure_set(v___f_4113_, 3, v_ctx_x3f_4107_);
lean_closure_set(v___f_4113_, 4, v_inst_4103_);
lean_closure_set(v___f_4113_, 5, v_getInfoState_4110_);
lean_closure_set(v___f_4113_, 6, v_inst_4105_);
lean_closure_set(v___f_4113_, 7, v_x_4106_);
lean_closure_set(v___f_4113_, 8, v___f_4112_);
v___f_4114_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4114_, 0, v_x_4106_);
lean_closure_set(v___f_4114_, 1, v_inst_4103_);
lean_closure_set(v___f_4114_, 2, v_inst_4104_);
lean_closure_set(v___f_4114_, 3, v_toBind_4109_);
lean_closure_set(v___f_4114_, 4, v___f_4113_);
v___x_4115_ = lean_apply_4(v_toBind_4109_, lean_box(0), lean_box(0), v_getInfoState_4110_, v___f_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4116_, lean_object* v_inst_4117_, lean_object* v_inst_4118_, lean_object* v_00_u03b1_4119_, lean_object* v_inst_4120_, lean_object* v_x_4121_, lean_object* v_ctx_x3f_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4117_, v_inst_4118_, v_inst_4120_, v_x_4121_, v_ctx_x3f_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4124_, lean_object* v_____do__lift_4125_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_____do__lift_4125_);
v___x_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
v___x_4128_ = lean_apply_2(v_toPure_4124_, lean_box(0), v___x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_inst_4133_, lean_object* v_inst_4134_, lean_object* v_inst_4135_, lean_object* v_inst_4136_, lean_object* v_inst_4137_, lean_object* v_x_4138_){
_start:
{
lean_object* v_toApplicative_4139_; lean_object* v_toBind_4140_; lean_object* v_toPure_4141_; lean_object* v___x_4142_; lean_object* v___f_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_toApplicative_4139_ = lean_ctor_get(v_inst_4129_, 0);
v_toBind_4140_ = lean_ctor_get(v_inst_4129_, 1);
v_toPure_4141_ = lean_ctor_get(v_toApplicative_4139_, 1);
lean_inc_ref(v_inst_4129_);
v___x_4142_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4129_, v_inst_4133_, v_inst_4135_, v_inst_4134_, v_inst_4136_, v_inst_4131_, v_inst_4137_);
lean_inc(v_toPure_4141_);
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4143_, 0, v_toPure_4141_);
lean_inc(v_toBind_4140_);
v___x_4144_ = lean_apply_4(v_toBind_4140_, lean_box(0), lean_box(0), v___x_4142_, v___f_4143_);
v___x_4145_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4129_, v_inst_4130_, v_inst_4132_, v_x_4138_, v___x_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4146_, lean_object* v_inst_4147_, lean_object* v_inst_4148_, lean_object* v_00_u03b1_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_inst_4152_, lean_object* v_inst_4153_, lean_object* v_inst_4154_, lean_object* v_inst_4155_, lean_object* v_inst_4156_, lean_object* v_x_4157_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4147_, v_inst_4148_, v_inst_4150_, v_inst_4151_, v_inst_4152_, v_inst_4153_, v_inst_4154_, v_inst_4155_, v_inst_4156_, v_x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4159_, lean_object* v_____x_4160_){
_start:
{
if (lean_obj_tag(v_____x_4160_) == 1)
{
lean_object* v_val_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4170_; 
v_val_4161_ = lean_ctor_get(v_____x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v_____x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4163_ = v_____x_4160_;
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_val_4161_);
lean_dec(v_____x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_val_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4167_ = v___x_4163_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_apply_2(v_toPure_4159_, lean_box(0), v___x_4167_);
return v___x_4168_;
}
}
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec(v_____x_4160_);
v___x_4171_ = lean_box(0);
v___x_4172_ = lean_apply_2(v_toPure_4159_, lean_box(0), v___x_4171_);
return v___x_4172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4173_, lean_object* v_inst_4174_, lean_object* v_inst_4175_, lean_object* v_inst_4176_, lean_object* v_x_4177_){
_start:
{
lean_object* v_toApplicative_4178_; lean_object* v_toBind_4179_; lean_object* v_toPure_4180_; lean_object* v___f_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_toApplicative_4178_ = lean_ctor_get(v_inst_4173_, 0);
v_toBind_4179_ = lean_ctor_get(v_inst_4173_, 1);
v_toPure_4180_ = lean_ctor_get(v_toApplicative_4178_, 1);
lean_inc(v_toPure_4180_);
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4181_, 0, v_toPure_4180_);
lean_inc(v_toBind_4179_);
v___x_4182_ = lean_apply_4(v_toBind_4179_, lean_box(0), lean_box(0), v_inst_4176_, v___f_4181_);
v___x_4183_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4173_, v_inst_4174_, v_inst_4175_, v_x_4177_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4184_, lean_object* v_inst_4185_, lean_object* v_inst_4186_, lean_object* v_00_u03b1_4187_, lean_object* v_inst_4188_, lean_object* v_inst_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4185_, v_inst_4186_, v_inst_4188_, v_inst_4189_, v_x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4192_, lean_object* v_autoImplicits_4193_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_autoImplicits_4193_);
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
v___x_4196_ = lean_apply_2(v_toPure_4192_, lean_box(0), v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_x_4201_){
_start:
{
lean_object* v_toApplicative_4202_; lean_object* v_toBind_4203_; lean_object* v_toPure_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_toApplicative_4202_ = lean_ctor_get(v_inst_4197_, 0);
v_toBind_4203_ = lean_ctor_get(v_inst_4197_, 1);
v_toPure_4204_ = lean_ctor_get(v_toApplicative_4202_, 1);
lean_inc(v_toPure_4204_);
v___f_4205_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4205_, 0, v_toPure_4204_);
lean_inc(v_toBind_4203_);
v___x_4206_ = lean_apply_4(v_toBind_4203_, lean_box(0), lean_box(0), v_inst_4200_, v___f_4205_);
v___x_4207_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4197_, v_inst_4198_, v_inst_4199_, v_x_4201_, v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4208_, lean_object* v_inst_4209_, lean_object* v_inst_4210_, lean_object* v_00_u03b1_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_x_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4209_, v_inst_4210_, v_inst_4212_, v_inst_4213_, v_x_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4216_, lean_object* v___x_4217_, lean_object* v_mvarId_4218_, lean_object* v_toPure_4219_, lean_object* v_____do__lift_4220_){
_start:
{
lean_object* v_assignment_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v_assignment_4221_ = lean_ctor_get(v_____do__lift_4220_, 0);
v___x_4222_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4216_, v___x_4217_, v_assignment_4221_, v_mvarId_4218_);
v___x_4223_ = lean_apply_2(v_toPure_4219_, lean_box(0), v___x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v_mvarId_4226_, lean_object* v_toPure_4227_, lean_object* v_____do__lift_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_4224_, v___x_4225_, v_mvarId_4226_, v_toPure_4227_, v_____do__lift_4228_);
lean_dec_ref(v_____do__lift_4228_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4232_, lean_object* v_inst_4233_, lean_object* v_mvarId_4234_){
_start:
{
lean_object* v_toApplicative_4235_; lean_object* v_toBind_4236_; lean_object* v_getInfoState_4237_; lean_object* v_toPure_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___f_4241_; lean_object* v___x_4242_; 
v_toApplicative_4235_ = lean_ctor_get(v_inst_4232_, 0);
lean_inc_ref(v_toApplicative_4235_);
v_toBind_4236_ = lean_ctor_get(v_inst_4232_, 1);
lean_inc(v_toBind_4236_);
lean_dec_ref(v_inst_4232_);
v_getInfoState_4237_ = lean_ctor_get(v_inst_4233_, 0);
lean_inc(v_getInfoState_4237_);
lean_dec_ref(v_inst_4233_);
v_toPure_4238_ = lean_ctor_get(v_toApplicative_4235_, 1);
lean_inc(v_toPure_4238_);
lean_dec_ref(v_toApplicative_4235_);
v___x_4239_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4240_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4241_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4241_, 0, v___x_4239_);
lean_closure_set(v___f_4241_, 1, v___x_4240_);
lean_closure_set(v___f_4241_, 2, v_mvarId_4234_);
lean_closure_set(v___f_4241_, 3, v_toPure_4238_);
v___x_4242_ = lean_apply_4(v_toBind_4236_, lean_box(0), lean_box(0), v_getInfoState_4237_, v___f_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_mvarId_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4244_, v_inst_4245_, v_mvarId_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4248_, lean_object* v_infoTree_4249_, lean_object* v_s_4250_){
_start:
{
uint8_t v_enabled_4251_; lean_object* v_assignment_4252_; lean_object* v_lazyAssignment_4253_; lean_object* v_trees_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4264_; 
v_enabled_4251_ = lean_ctor_get_uint8(v_s_4250_, sizeof(void*)*3);
v_assignment_4252_ = lean_ctor_get(v_s_4250_, 0);
v_lazyAssignment_4253_ = lean_ctor_get(v_s_4250_, 1);
v_trees_4254_ = lean_ctor_get(v_s_4250_, 2);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_s_4250_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4256_ = v_s_4250_;
v_isShared_4257_ = v_isSharedCheck_4264_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_trees_4254_);
lean_inc(v_lazyAssignment_4253_);
lean_inc(v_assignment_4252_);
lean_dec(v_s_4250_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4264_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4258_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4259_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4260_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4258_, v___x_4259_, v_assignment_4252_, v_mvarId_4248_, v_infoTree_4249_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4260_);
v___x_4262_ = v___x_4256_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_lazyAssignment_4253_);
lean_ctor_set(v_reuseFailAlloc_4263_, 2, v_trees_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4263_, sizeof(void*)*3, v_enabled_4251_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4267_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4268_ = lean_unsigned_to_nat(2u);
v___x_4269_ = lean_unsigned_to_nat(491u);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4271_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4272_ = l_mkPanicMessageWithDecl(v___x_4271_, v___x_4270_, v___x_4269_, v___x_4268_, v___x_4267_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4273_, lean_object* v___f_4274_, lean_object* v_inst_4275_, lean_object* v_____do__lift_4276_){
_start:
{
if (lean_obj_tag(v_____do__lift_4276_) == 0)
{
lean_object* v_modifyInfoState_4277_; lean_object* v___x_4278_; 
lean_dec_ref(v_inst_4275_);
v_modifyInfoState_4277_ = lean_ctor_get(v_inst_4273_, 1);
lean_inc(v_modifyInfoState_4277_);
lean_dec_ref(v_inst_4273_);
v___x_4278_ = lean_apply_1(v_modifyInfoState_4277_, v___f_4274_);
return v___x_4278_;
}
else
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_dec_ref(v___f_4274_);
lean_dec_ref(v_inst_4273_);
v___x_4279_ = lean_box(0);
v___x_4280_ = l_instInhabitedOfMonad___redArg(v_inst_4275_, v___x_4279_);
v___x_4281_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4282_ = l_panic___redArg(v___x_4280_, v___x_4281_);
lean_dec(v___x_4280_);
return v___x_4282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4283_, lean_object* v___f_4284_, lean_object* v_inst_4285_, lean_object* v_____do__lift_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4283_, v___f_4284_, v_inst_4285_, v_____do__lift_4286_);
lean_dec(v_____do__lift_4286_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4288_, lean_object* v_inst_4289_, lean_object* v_mvarId_4290_, lean_object* v_infoTree_4291_){
_start:
{
lean_object* v_toBind_4292_; lean_object* v___f_4293_; lean_object* v___f_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v_toBind_4292_ = lean_ctor_get(v_inst_4288_, 1);
lean_inc(v_toBind_4292_);
lean_inc(v_mvarId_4290_);
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4293_, 0, v_mvarId_4290_);
lean_closure_set(v___f_4293_, 1, v_infoTree_4291_);
lean_inc_ref(v_inst_4288_);
lean_inc_ref(v_inst_4289_);
v___f_4294_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4294_, 0, v_inst_4289_);
lean_closure_set(v___f_4294_, 1, v___f_4293_);
lean_closure_set(v___f_4294_, 2, v_inst_4288_);
v___x_4295_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4288_, v_inst_4289_, v_mvarId_4290_);
v___x_4296_ = lean_apply_4(v_toBind_4292_, lean_box(0), lean_box(0), v___x_4295_, v___f_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4297_, lean_object* v_inst_4298_, lean_object* v_inst_4299_, lean_object* v_mvarId_4300_, lean_object* v_infoTree_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4298_, v_inst_4299_, v_mvarId_4300_, v_infoTree_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4303_, lean_object* v_output_4304_, lean_object* v_toPure_4305_, lean_object* v_____do__lift_4306_){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4307_, 0, v_____do__lift_4306_);
lean_ctor_set(v___x_4307_, 1, v_stx_4303_);
lean_ctor_set(v___x_4307_, 2, v_output_4304_);
v___x_4308_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
v___x_4309_ = lean_apply_2(v_toPure_4305_, lean_box(0), v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_inst_4313_, lean_object* v_stx_4314_, lean_object* v_output_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v_toApplicative_4317_; lean_object* v_toBind_4318_; lean_object* v_toPure_4319_; lean_object* v___f_4320_; lean_object* v_mkInfo_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
v_toApplicative_4317_ = lean_ctor_get(v_inst_4311_, 0);
v_toBind_4318_ = lean_ctor_get(v_inst_4311_, 1);
v_toPure_4319_ = lean_ctor_get(v_toApplicative_4317_, 1);
lean_inc_n(v_toPure_4319_, 2);
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4320_, 0, v_stx_4314_);
lean_closure_set(v___f_4320_, 1, v_output_4315_);
lean_closure_set(v___f_4320_, 2, v_toPure_4319_);
lean_inc_n(v_toBind_4318_, 2);
v_mkInfo_4321_ = lean_apply_4(v_toBind_4318_, lean_box(0), lean_box(0), v_inst_4313_, v___f_4320_);
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4322_, 0, v_toPure_4319_);
lean_closure_set(v___f_4322_, 1, v_toBind_4318_);
lean_closure_set(v___f_4322_, 2, v_mkInfo_4321_);
v___x_4323_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4311_, v_inst_4312_, v_inst_4310_, v_x_4316_, v___f_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4324_, lean_object* v_00_u03b1_4325_, lean_object* v_inst_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_, lean_object* v_inst_4329_, lean_object* v_stx_4330_, lean_object* v_output_4331_, lean_object* v_x_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4326_, v_inst_4327_, v_inst_4328_, v_inst_4329_, v_stx_4330_, v_output_4331_, v_x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4334_, lean_object* v_mvarId_4335_, lean_object* v_s_4336_){
_start:
{
lean_object* v_trees_4337_; uint8_t v_enabled_4338_; lean_object* v_assignment_4339_; lean_object* v_lazyAssignment_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4360_; 
v_trees_4337_ = lean_ctor_get(v_s_4336_, 2);
v_enabled_4338_ = lean_ctor_get_uint8(v_s_4336_, sizeof(void*)*3);
v_assignment_4339_ = lean_ctor_get(v_s_4336_, 0);
v_lazyAssignment_4340_ = lean_ctor_get(v_s_4336_, 1);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_s_4336_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4342_ = v_s_4336_;
v_isShared_4343_ = v_isSharedCheck_4360_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_trees_4337_);
lean_inc(v_lazyAssignment_4340_);
lean_inc(v_assignment_4339_);
lean_dec(v_s_4336_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4360_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v_size_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v_size_4344_ = lean_ctor_get(v_trees_4337_, 2);
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_nat_dec_lt(v___x_4345_, v_size_4344_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4348_; 
lean_dec_ref(v_trees_4337_);
lean_dec(v_mvarId_4335_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 2, v_treesSaved_4334_);
v___x_4348_ = v___x_4342_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_assignment_4339_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_lazyAssignment_4340_);
lean_ctor_set(v_reuseFailAlloc_4349_, 2, v_treesSaved_4334_);
lean_ctor_set_uint8(v_reuseFailAlloc_4349_, sizeof(void*)*3, v_enabled_4338_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
v___x_4350_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4351_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4352_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4353_ = lean_unsigned_to_nat(1u);
v___x_4354_ = lean_nat_sub(v_size_4344_, v___x_4353_);
v___x_4355_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4352_, v_trees_4337_, v___x_4354_);
lean_dec(v___x_4354_);
lean_dec_ref(v_trees_4337_);
v___x_4356_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4350_, v___x_4351_, v_assignment_4339_, v_mvarId_4335_, v___x_4355_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 2, v_treesSaved_4334_);
lean_ctor_set(v___x_4342_, 0, v___x_4356_);
v___x_4358_ = v___x_4342_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_lazyAssignment_4340_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_treesSaved_4334_);
lean_ctor_set_uint8(v_reuseFailAlloc_4359_, sizeof(void*)*3, v_enabled_4338_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4361_, lean_object* v___f_4362_, lean_object* v_x_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_apply_1(v_modifyInfoState_4361_, v___f_4362_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4365_, lean_object* v___f_4366_, lean_object* v_x_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4365_, v___f_4366_, v_x_4367_);
lean_dec(v_x_4367_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4369_, lean_object* v_mvarId_4370_, lean_object* v_modifyInfoState_4371_, lean_object* v_inst_4372_, lean_object* v_x_4373_, lean_object* v___f_4374_, lean_object* v_treesSaved_4375_){
_start:
{
lean_object* v_toFunctor_4376_; lean_object* v_map_4377_; lean_object* v___f_4378_; lean_object* v___f_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v_toFunctor_4376_ = lean_ctor_get(v_toApplicative_4369_, 0);
lean_inc_ref(v_toFunctor_4376_);
lean_dec_ref(v_toApplicative_4369_);
v_map_4377_ = lean_ctor_get(v_toFunctor_4376_, 0);
lean_inc(v_map_4377_);
lean_dec_ref(v_toFunctor_4376_);
v___f_4378_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4378_, 0, v_treesSaved_4375_);
lean_closure_set(v___f_4378_, 1, v_mvarId_4370_);
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4379_, 0, v_modifyInfoState_4371_);
lean_closure_set(v___f_4379_, 1, v___f_4378_);
v___x_4380_ = lean_apply_4(v_inst_4372_, lean_box(0), lean_box(0), v_x_4373_, v___f_4379_);
v___x_4381_ = lean_apply_4(v_map_4377_, lean_box(0), lean_box(0), v___f_4374_, v___x_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4382_, lean_object* v_inst_4383_, lean_object* v_inst_4384_, lean_object* v_mvarId_4385_, lean_object* v_x_4386_){
_start:
{
lean_object* v_toApplicative_4387_; lean_object* v_toBind_4388_; lean_object* v_getInfoState_4389_; lean_object* v_modifyInfoState_4390_; lean_object* v___f_4391_; lean_object* v___f_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; 
v_toApplicative_4387_ = lean_ctor_get(v_inst_4383_, 0);
v_toBind_4388_ = lean_ctor_get(v_inst_4383_, 1);
lean_inc_n(v_toBind_4388_, 2);
v_getInfoState_4389_ = lean_ctor_get(v_inst_4384_, 0);
lean_inc(v_getInfoState_4389_);
v_modifyInfoState_4390_ = lean_ctor_get(v_inst_4384_, 1);
v___f_4391_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4386_);
lean_inc(v_modifyInfoState_4390_);
lean_inc_ref(v_toApplicative_4387_);
v___f_4392_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4392_, 0, v_toApplicative_4387_);
lean_closure_set(v___f_4392_, 1, v_mvarId_4385_);
lean_closure_set(v___f_4392_, 2, v_modifyInfoState_4390_);
lean_closure_set(v___f_4392_, 3, v_inst_4382_);
lean_closure_set(v___f_4392_, 4, v_x_4386_);
lean_closure_set(v___f_4392_, 5, v___f_4391_);
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4393_, 0, v_x_4386_);
lean_closure_set(v___f_4393_, 1, v_inst_4383_);
lean_closure_set(v___f_4393_, 2, v_inst_4384_);
lean_closure_set(v___f_4393_, 3, v_toBind_4388_);
lean_closure_set(v___f_4393_, 4, v___f_4392_);
v___x_4394_ = lean_apply_4(v_toBind_4388_, lean_box(0), lean_box(0), v_getInfoState_4389_, v___f_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4395_, lean_object* v_00_u03b1_4396_, lean_object* v_inst_4397_, lean_object* v_inst_4398_, lean_object* v_inst_4399_, lean_object* v_mvarId_4400_, lean_object* v_x_4401_){
_start:
{
lean_object* v_toApplicative_4402_; lean_object* v_toBind_4403_; lean_object* v_getInfoState_4404_; lean_object* v_modifyInfoState_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___f_4408_; lean_object* v___x_4409_; 
v_toApplicative_4402_ = lean_ctor_get(v_inst_4398_, 0);
v_toBind_4403_ = lean_ctor_get(v_inst_4398_, 1);
lean_inc_n(v_toBind_4403_, 2);
v_getInfoState_4404_ = lean_ctor_get(v_inst_4399_, 0);
lean_inc(v_getInfoState_4404_);
v_modifyInfoState_4405_ = lean_ctor_get(v_inst_4399_, 1);
v___f_4406_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4401_);
lean_inc(v_modifyInfoState_4405_);
lean_inc_ref(v_toApplicative_4402_);
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4407_, 0, v_toApplicative_4402_);
lean_closure_set(v___f_4407_, 1, v_mvarId_4400_);
lean_closure_set(v___f_4407_, 2, v_modifyInfoState_4405_);
lean_closure_set(v___f_4407_, 3, v_inst_4397_);
lean_closure_set(v___f_4407_, 4, v_x_4401_);
lean_closure_set(v___f_4407_, 5, v___f_4406_);
v___f_4408_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4408_, 0, v_x_4401_);
lean_closure_set(v___f_4408_, 1, v_inst_4398_);
lean_closure_set(v___f_4408_, 2, v_inst_4399_);
lean_closure_set(v___f_4408_, 3, v_toBind_4403_);
lean_closure_set(v___f_4408_, 4, v___f_4407_);
v___x_4409_ = lean_apply_4(v_toBind_4403_, lean_box(0), lean_box(0), v_getInfoState_4404_, v___f_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4410_, lean_object* v_s_4411_){
_start:
{
lean_object* v_assignment_4412_; lean_object* v_lazyAssignment_4413_; lean_object* v_trees_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_assignment_4412_ = lean_ctor_get(v_s_4411_, 0);
v_lazyAssignment_4413_ = lean_ctor_get(v_s_4411_, 1);
v_trees_4414_ = lean_ctor_get(v_s_4411_, 2);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_s_4411_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v_s_4411_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_trees_4414_);
lean_inc(v_lazyAssignment_4413_);
lean_inc(v_assignment_4412_);
lean_dec(v_s_4411_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_assignment_4412_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_lazyAssignment_4413_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v_trees_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*3, v_flag_4410_);
return v___x_4419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4422_, lean_object* v_s_4423_){
_start:
{
uint8_t v_flag_boxed_4424_; lean_object* v_res_4425_; 
v_flag_boxed_4424_ = lean_unbox(v_flag_4422_);
v_res_4425_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4424_, v_s_4423_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4426_, uint8_t v_flag_4427_){
_start:
{
lean_object* v_modifyInfoState_4428_; lean_object* v___x_4429_; lean_object* v___f_4430_; lean_object* v___x_4431_; 
v_modifyInfoState_4428_ = lean_ctor_get(v_inst_4426_, 1);
lean_inc(v_modifyInfoState_4428_);
lean_dec_ref(v_inst_4426_);
v___x_4429_ = lean_box(v_flag_4427_);
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4430_, 0, v___x_4429_);
v___x_4431_ = lean_apply_1(v_modifyInfoState_4428_, v___f_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4432_, lean_object* v_flag_4433_){
_start:
{
uint8_t v_flag_boxed_4434_; lean_object* v_res_4435_; 
v_flag_boxed_4434_ = lean_unbox(v_flag_4433_);
v_res_4435_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4432_, v_flag_boxed_4434_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4436_, lean_object* v_inst_4437_, uint8_t v_flag_4438_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4437_, v_flag_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4440_, lean_object* v_inst_4441_, lean_object* v_flag_4442_){
_start:
{
uint8_t v_flag_boxed_4443_; lean_object* v_res_4444_; 
v_flag_boxed_4443_ = lean_unbox(v_flag_4442_);
v_res_4444_ = l_Lean_Elab_enableInfoTree(v_m_4440_, v_inst_4441_, v_flag_boxed_4443_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4445_){
_start:
{
lean_object* v_fst_4446_; 
v_fst_4446_ = lean_ctor_get(v_x_4445_, 0);
lean_inc(v_fst_4446_);
return v_fst_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4447_);
lean_dec_ref(v_x_4447_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4449_, lean_object* v_____r_4450_){
_start:
{
lean_inc(v_x_4449_);
return v_x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4451_, lean_object* v_____r_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4451_, v_____r_4452_);
lean_dec(v_x_4451_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4454_, lean_object* v_x_4455_){
_start:
{
lean_inc(v___x_4454_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4456_, lean_object* v_x_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4456_, v_x_4457_);
lean_dec(v_x_4457_);
lean_dec(v___x_4456_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4459_, lean_object* v_inst_4460_, uint8_t v_flag_4461_, lean_object* v_toBind_4462_, lean_object* v___f_4463_, lean_object* v_inst_4464_, lean_object* v___f_4465_, lean_object* v_____do__lift_4466_){
_start:
{
uint8_t v_enabled_4467_; lean_object* v_map_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___f_4472_; lean_object* v_y_4473_; lean_object* v___x_4474_; 
v_enabled_4467_ = lean_ctor_get_uint8(v_____do__lift_4466_, sizeof(void*)*3);
v_map_4468_ = lean_ctor_get(v_toFunctor_4459_, 0);
lean_inc(v_map_4468_);
lean_dec_ref(v_toFunctor_4459_);
lean_inc_ref(v_inst_4460_);
v___x_4469_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4460_, v_flag_4461_);
v___x_4470_ = lean_apply_4(v_toBind_4462_, lean_box(0), lean_box(0), v___x_4469_, v___f_4463_);
v___x_4471_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4460_, v_enabled_4467_);
v___f_4472_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4472_, 0, v___x_4471_);
v_y_4473_ = lean_apply_4(v_inst_4464_, lean_box(0), lean_box(0), v___x_4470_, v___f_4472_);
v___x_4474_ = lean_apply_4(v_map_4468_, lean_box(0), lean_box(0), v___f_4465_, v_y_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4475_, lean_object* v_inst_4476_, lean_object* v_flag_4477_, lean_object* v_toBind_4478_, lean_object* v___f_4479_, lean_object* v_inst_4480_, lean_object* v___f_4481_, lean_object* v_____do__lift_4482_){
_start:
{
uint8_t v_flag_boxed_4483_; lean_object* v_res_4484_; 
v_flag_boxed_4483_ = lean_unbox(v_flag_4477_);
v_res_4484_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4475_, v_inst_4476_, v_flag_boxed_4483_, v_toBind_4478_, v___f_4479_, v_inst_4480_, v___f_4481_, v_____do__lift_4482_);
lean_dec_ref(v_____do__lift_4482_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4486_, lean_object* v_inst_4487_, lean_object* v_inst_4488_, uint8_t v_flag_4489_, lean_object* v_x_4490_){
_start:
{
lean_object* v_toApplicative_4491_; lean_object* v_toBind_4492_; lean_object* v_getInfoState_4493_; lean_object* v_toFunctor_4494_; lean_object* v___f_4495_; lean_object* v___f_4496_; lean_object* v___x_4497_; lean_object* v___f_4498_; lean_object* v___x_4499_; 
v_toApplicative_4491_ = lean_ctor_get(v_inst_4486_, 0);
lean_inc_ref(v_toApplicative_4491_);
v_toBind_4492_ = lean_ctor_get(v_inst_4486_, 1);
lean_inc_n(v_toBind_4492_, 2);
lean_dec_ref(v_inst_4486_);
v_getInfoState_4493_ = lean_ctor_get(v_inst_4487_, 0);
lean_inc(v_getInfoState_4493_);
v_toFunctor_4494_ = lean_ctor_get(v_toApplicative_4491_, 0);
lean_inc_ref(v_toFunctor_4494_);
lean_dec_ref(v_toApplicative_4491_);
v___f_4495_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4496_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4496_, 0, v_x_4490_);
v___x_4497_ = lean_box(v_flag_4489_);
v___f_4498_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4498_, 0, v_toFunctor_4494_);
lean_closure_set(v___f_4498_, 1, v_inst_4487_);
lean_closure_set(v___f_4498_, 2, v___x_4497_);
lean_closure_set(v___f_4498_, 3, v_toBind_4492_);
lean_closure_set(v___f_4498_, 4, v___f_4496_);
lean_closure_set(v___f_4498_, 5, v_inst_4488_);
lean_closure_set(v___f_4498_, 6, v___f_4495_);
v___x_4499_ = lean_apply_4(v_toBind_4492_, lean_box(0), lean_box(0), v_getInfoState_4493_, v___f_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4500_, lean_object* v_inst_4501_, lean_object* v_inst_4502_, lean_object* v_flag_4503_, lean_object* v_x_4504_){
_start:
{
uint8_t v_flag_boxed_4505_; lean_object* v_res_4506_; 
v_flag_boxed_4505_ = lean_unbox(v_flag_4503_);
v_res_4506_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4500_, v_inst_4501_, v_inst_4502_, v_flag_boxed_4505_, v_x_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4507_, lean_object* v_00_u03b1_4508_, lean_object* v_inst_4509_, lean_object* v_inst_4510_, lean_object* v_inst_4511_, uint8_t v_flag_4512_, lean_object* v_x_4513_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4509_, v_inst_4510_, v_inst_4511_, v_flag_4512_, v_x_4513_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4515_, lean_object* v_00_u03b1_4516_, lean_object* v_inst_4517_, lean_object* v_inst_4518_, lean_object* v_inst_4519_, lean_object* v_flag_4520_, lean_object* v_x_4521_){
_start:
{
uint8_t v_flag_boxed_4522_; lean_object* v_res_4523_; 
v_flag_boxed_4522_ = lean_unbox(v_flag_4520_);
v_res_4523_ = l_Lean_Elab_withEnableInfoTree(v_m_4515_, v_00_u03b1_4516_, v_inst_4517_, v_inst_4518_, v_inst_4519_, v_flag_boxed_4522_, v_x_4521_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4524_, lean_object* v_____do__lift_4525_){
_start:
{
lean_object* v_trees_4526_; lean_object* v___x_4527_; 
v_trees_4526_ = lean_ctor_get(v_____do__lift_4525_, 2);
lean_inc_ref(v_trees_4526_);
lean_dec_ref(v_____do__lift_4525_);
v___x_4527_ = lean_apply_2(v_toPure_4524_, lean_box(0), v_trees_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4528_, lean_object* v_inst_4529_){
_start:
{
lean_object* v_toApplicative_4530_; lean_object* v_toBind_4531_; lean_object* v_getInfoState_4532_; lean_object* v_toPure_4533_; lean_object* v___f_4534_; lean_object* v___x_4535_; 
v_toApplicative_4530_ = lean_ctor_get(v_inst_4529_, 0);
lean_inc_ref(v_toApplicative_4530_);
v_toBind_4531_ = lean_ctor_get(v_inst_4529_, 1);
lean_inc(v_toBind_4531_);
lean_dec_ref(v_inst_4529_);
v_getInfoState_4532_ = lean_ctor_get(v_inst_4528_, 0);
lean_inc(v_getInfoState_4532_);
lean_dec_ref(v_inst_4528_);
v_toPure_4533_ = lean_ctor_get(v_toApplicative_4530_, 1);
lean_inc(v_toPure_4533_);
lean_dec_ref(v_toApplicative_4530_);
v___f_4534_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4534_, 0, v_toPure_4533_);
v___x_4535_ = lean_apply_4(v_toBind_4531_, lean_box(0), lean_box(0), v_getInfoState_4532_, v___f_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4536_, lean_object* v_inst_4537_, lean_object* v_inst_4538_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4537_, v_inst_4538_);
return v___x_4539_;
}
}
lean_object* runtime_initialize_Init_Task(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Task(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_InfoTree_Main(builtin);
}
#ifdef __cplusplus
}
#endif
