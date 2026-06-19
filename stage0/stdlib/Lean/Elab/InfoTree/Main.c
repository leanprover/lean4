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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1;
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; 
v___x_404_ = ((size_t)5ULL);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_shift_left(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; 
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0);
v___x_409_ = lean_usize_sub(v___x_408_, v___x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(lean_object* v_x_410_, size_t v_x_411_, lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_es_413_; lean_object* v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_j_418_; lean_object* v___x_419_; 
v_es_413_ = lean_ctor_get(v_x_410_, 0);
v___x_414_ = lean_box(2);
v___x_415_ = ((size_t)5ULL);
v___x_416_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1);
v___x_417_ = lean_usize_land(v_x_411_, v___x_416_);
v_j_418_ = lean_usize_to_nat(v___x_417_);
v___x_419_ = lean_array_get_borrowed(v___x_414_, v_es_413_, v_j_418_);
lean_dec(v_j_418_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_key_420_; lean_object* v_val_421_; uint8_t v___x_422_; 
v_key_420_ = lean_ctor_get(v___x_419_, 0);
v_val_421_ = lean_ctor_get(v___x_419_, 1);
v___x_422_ = l_Lean_instBEqMVarId_beq(v_x_412_, v_key_420_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_inc(v_val_421_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_val_421_);
return v___x_424_;
}
}
case 1:
{
lean_object* v_node_425_; size_t v___x_426_; 
v_node_425_ = lean_ctor_get(v___x_419_, 0);
v___x_426_ = lean_usize_shift_right(v_x_411_, v___x_415_);
v_x_410_ = v_node_425_;
v_x_411_ = v___x_426_;
goto _start;
}
default: 
{
lean_object* v___x_428_; 
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
}
else
{
lean_object* v_ks_429_; lean_object* v_vs_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_ks_429_ = lean_ctor_get(v_x_410_, 0);
v_vs_430_ = lean_ctor_get(v_x_410_, 1);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_ks_429_, v_vs_430_, v___x_431_, v_x_412_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___boxed(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
size_t v_x_693__boxed_436_; lean_object* v_res_437_; 
v_x_693__boxed_436_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_433_, v_x_693__boxed_436_, v_x_435_);
lean_dec(v_x_435_);
lean_dec_ref(v_x_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint64_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_instHashableMVarId_hash(v_x_439_);
v___x_441_ = lean_uint64_to_usize(v___x_440_);
v___x_442_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_438_, v___x_441_, v_x_439_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg___boxed(lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_443_, v_x_444_);
lean_dec(v_x_444_);
lean_dec_ref(v_x_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(lean_object* v_assignment_446_, size_t v_sz_447_, size_t v_i_448_, lean_object* v_bs_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_lt(v_i_448_, v_sz_447_);
if (v___x_450_ == 0)
{
return v_bs_449_;
}
else
{
lean_object* v_v_451_; lean_object* v___x_452_; lean_object* v_bs_x27_453_; lean_object* v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
v_v_451_ = lean_array_uget(v_bs_449_, v_i_448_);
v___x_452_ = lean_unsigned_to_nat(0u);
v_bs_x27_453_ = lean_array_uset(v_bs_449_, v_i_448_, v___x_452_);
v___x_454_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_446_, v_v_451_);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_448_, v___x_455_);
v___x_457_ = lean_array_uset(v_bs_x27_453_, v_i_448_, v___x_454_);
v_i_448_ = v___x_456_;
v_bs_449_ = v___x_457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute(lean_object* v_tree_459_, lean_object* v_assignment_460_){
_start:
{
switch(lean_obj_tag(v_tree_459_))
{
case 0:
{
lean_object* v_i_461_; lean_object* v_t_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_i_461_ = lean_ctor_get(v_tree_459_, 0);
v_t_462_ = lean_ctor_get(v_tree_459_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_tree_459_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v_tree_459_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_t_462_);
lean_inc(v_i_461_);
lean_dec(v_tree_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_Elab_InfoTree_substitute(v_t_462_, v_assignment_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_i_461_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
case 1:
{
lean_object* v_i_471_; lean_object* v_children_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_i_471_ = lean_ctor_get(v_tree_459_, 0);
v_children_472_ = lean_ctor_get(v_tree_459_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_tree_459_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v_tree_459_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_children_472_);
lean_inc(v_i_471_);
lean_dec(v_tree_459_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(v_assignment_460_, v_children_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_i_471_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
default: 
{
lean_object* v_mvarId_481_; lean_object* v___x_482_; 
v_mvarId_481_ = lean_ctor_get(v_tree_459_, 0);
v___x_482_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_assignment_460_, v_mvarId_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
return v_tree_459_;
}
else
{
lean_object* v_val_483_; 
lean_dec_ref_known(v_tree_459_, 1);
v_val_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_482_, 1);
v_tree_459_ = v_val_483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(lean_object* v_assignment_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_489_ == 0)
{
return v_bs_488_;
}
else
{
lean_object* v_v_490_; lean_object* v___x_491_; lean_object* v_bs_x27_492_; lean_object* v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v_v_490_ = lean_array_uget(v_bs_488_, v_i_487_);
v___x_491_ = lean_unsigned_to_nat(0u);
v_bs_x27_492_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_491_);
v___x_493_ = l_Lean_Elab_InfoTree_substitute(v_v_490_, v_assignment_485_);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_487_, v___x_494_);
v___x_496_ = lean_array_uset(v_bs_x27_492_, v_i_487_, v___x_493_);
v_i_487_ = v___x_495_;
v_bs_488_ = v___x_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(lean_object* v_assignment_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_cs_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_cs_500_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v_x_499_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_cs_500_);
lean_dec(v_x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
size_t v_sz_504_; size_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v_sz_504_ = lean_array_size(v_cs_500_);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_498_, v_sz_504_, v___x_505_, v_cs_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_object* v_vs_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_521_; 
v_vs_511_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_521_ == 0)
{
v___x_513_ = v_x_499_;
v_isShared_514_ = v_isSharedCheck_521_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_vs_511_);
lean_dec(v_x_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_521_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
size_t v_sz_515_; size_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v_sz_515_ = lean_array_size(v_vs_511_);
v___x_516_ = ((size_t)0ULL);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_498_, v_sz_515_, v___x_516_, v_vs_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_517_);
v___x_519_ = v___x_513_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(lean_object* v_assignment_522_, lean_object* v_t_523_){
_start:
{
lean_object* v_root_524_; lean_object* v_tail_525_; lean_object* v_size_526_; size_t v_shift_527_; lean_object* v_tailOff_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_root_524_ = lean_ctor_get(v_t_523_, 0);
v_tail_525_ = lean_ctor_get(v_t_523_, 1);
v_size_526_ = lean_ctor_get(v_t_523_, 2);
v_shift_527_ = lean_ctor_get_usize(v_t_523_, 4);
v_tailOff_528_ = lean_ctor_get(v_t_523_, 3);
v_isSharedCheck_539_ = !lean_is_exclusive(v_t_523_);
if (v_isSharedCheck_539_ == 0)
{
v___x_530_ = v_t_523_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_tailOff_528_);
lean_inc(v_size_526_);
lean_inc(v_tail_525_);
lean_inc(v_root_524_);
lean_dec(v_t_523_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; size_t v_sz_533_; size_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_532_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_522_, v_root_524_);
v_sz_533_ = lean_array_size(v_tail_525_);
v___x_534_ = ((size_t)0ULL);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_522_, v_sz_533_, v___x_534_, v_tail_525_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___x_535_);
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_537_ = v___x_530_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_size_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_tailOff_528_);
lean_ctor_set_usize(v_reuseFailAlloc_538_, 4, v_shift_527_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0___boxed(lean_object* v_assignment_540_, lean_object* v_t_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(v_assignment_540_, v_t_541_);
lean_dec_ref(v_assignment_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0___boxed(lean_object* v_assignment_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_543_, v_x_544_);
lean_dec_ref(v_assignment_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1___boxed(lean_object* v_assignment_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_546_, v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
lean_dec_ref(v_assignment_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1___boxed(lean_object* v_assignment_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_bs_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_553_, v_sz_boxed_557_, v_i_boxed_558_, v_bs_556_);
lean_dec_ref(v_assignment_553_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute___boxed(lean_object* v_tree_560_, lean_object* v_assignment_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Elab_InfoTree_substitute(v_tree_560_, v_assignment_561_);
lean_dec_ref(v_assignment_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(lean_object* v_00_u03b2_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_564_, v_x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___boxed(lean_object* v_00_u03b2_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(v_00_u03b2_567_, v_x_568_, v_x_569_);
lean_dec(v_x_569_);
lean_dec_ref(v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, size_t v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_572_, v_x_573_, v_x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___boxed(lean_object* v_00_u03b2_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
size_t v_x_905__boxed_580_; lean_object* v_res_581_; 
v_x_905__boxed_580_ = lean_unbox_usize(v_x_578_);
lean_dec(v_x_578_);
v_res_581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(v_00_u03b2_576_, v_x_577_, v_x_905__boxed_580_, v_x_579_);
lean_dec(v_x_579_);
lean_dec_ref(v_x_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_582_, lean_object* v_keys_583_, lean_object* v_vals_584_, lean_object* v_heq_585_, lean_object* v_i_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_583_, v_vals_584_, v_i_586_, v_k_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_589_, lean_object* v_keys_590_, lean_object* v_vals_591_, lean_object* v_heq_592_, lean_object* v_i_593_, lean_object* v_k_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(v_00_u03b2_589_, v_keys_590_, v_vals_591_, v_heq_592_, v_i_593_, v_k_594_);
lean_dec(v_k_594_);
lean_dec_ref(v_vals_591_);
lean_dec_ref(v_keys_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(lean_object* v_f_596_, lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_acc_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_as_597_);
v___x_601_ = lean_nat_dec_eq(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = lean_array_fget_borrowed(v_as_597_, v_i_598_);
lean_inc(v_f_596_);
lean_inc(v___x_602_);
v___x_603_ = lean_apply_1(v_f_596_, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_598_, v___x_604_);
lean_dec(v_i_598_);
v___x_606_ = lean_array_push(v_acc_599_, v___x_603_);
v_i_598_ = v___x_605_;
v_acc_599_ = v___x_606_;
goto _start;
}
else
{
lean_dec(v_i_598_);
lean_dec(v_f_596_);
return v_acc_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_f_608_, lean_object* v_as_609_, lean_object* v_i_610_, lean_object* v_acc_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_608_, v_as_609_, v_i_610_, v_acc_611_);
lean_dec_ref(v_as_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_613_, lean_object* v_as_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_as_614_);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_613_, v_as_614_, v___x_615_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_619_, lean_object* v_as_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_619_, v_as_620_);
lean_dec_ref(v_as_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_bs_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_626_ == 0)
{
lean_dec(v_f_622_);
return v_bs_625_;
}
else
{
lean_object* v_v_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; lean_object* v___y_631_; 
v_v_627_ = lean_array_uget(v_bs_625_, v_i_624_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_625_, v_i_624_, v___x_628_);
switch(lean_obj_tag(v_v_627_))
{
case 0:
{
lean_object* v_key_636_; lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_key_636_ = lean_ctor_get(v_v_627_, 0);
v_val_637_ = lean_ctor_get(v_v_627_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_v_627_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v_v_627_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_inc(v_key_636_);
lean_dec(v_v_627_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_f_622_);
v___x_641_ = lean_apply_1(v_f_622_, v_val_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_631_ = v___x_643_;
goto v___jp_630_;
}
}
}
case 1:
{
lean_object* v_node_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_node_646_ = lean_ctor_get(v_v_627_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_v_627_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_v_627_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_node_646_);
lean_dec(v_v_627_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc(v_f_622_);
v___x_650_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_622_, v_node_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v___y_631_ = v___x_652_;
goto v___jp_630_;
}
}
}
default: 
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(2);
v___y_631_ = v___x_655_;
goto v___jp_630_;
}
}
v___jp_630_:
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_624_, v___x_632_);
v___x_634_ = lean_array_uset(v_bs_x27_629_, v_i_624_, v___y_631_);
v_i_624_ = v___x_633_;
v_bs_625_ = v___x_634_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(lean_object* v_f_656_, lean_object* v_n_657_){
_start:
{
if (lean_obj_tag(v_n_657_) == 0)
{
lean_object* v_es_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_es_658_ = lean_ctor_get(v_n_657_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_n_657_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v_n_657_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_es_658_);
lean_dec(v_n_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_sz_662_ = lean_array_size(v_es_658_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_656_, v_sz_662_, v___x_663_, v_es_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_ks_669_; lean_object* v_vs_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_ks_669_ = lean_ctor_get(v_n_657_, 0);
v_vs_670_ = lean_ctor_get(v_n_657_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_n_657_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_n_657_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_vs_670_);
lean_inc(v_ks_669_);
lean_dec(v_n_657_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_val_674_; lean_object* v___x_676_; 
v_val_674_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_656_, v_vs_670_);
lean_dec_ref(v_vs_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_val_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_ks_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_val_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_bs_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_684_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_679_, v_sz_boxed_683_, v_i_boxed_684_, v_bs_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0(lean_object* v_f_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_apply_1(v_f_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(lean_object* v_pm_689_, lean_object* v_f_690_){
_start:
{
lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_691_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_691_, 0, v_f_690_);
v___x_692_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v___f_691_, v_pm_689_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0(lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_task_get_own(v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(lean_object* v_s_696_, size_t v_sz_697_, size_t v_i_698_, lean_object* v_bs_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_700_ == 0)
{
lean_dec_ref(v_s_696_);
return v_bs_699_;
}
else
{
lean_object* v_lazyAssignment_701_; lean_object* v_v_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; lean_object* v___x_706_; lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v_lazyAssignment_701_ = lean_ctor_get(v_s_696_, 1);
v_v_702_ = lean_array_uget(v_bs_699_, v_i_698_);
v___f_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0));
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_699_, v_i_698_, v___x_704_);
lean_inc_ref(v_lazyAssignment_701_);
v___x_706_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_lazyAssignment_701_, v___f_703_);
v___x_707_ = l_Lean_Elab_InfoTree_substitute(v_v_702_, v___x_706_);
lean_dec_ref(v___x_706_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_698_, v___x_708_);
v___x_710_ = lean_array_uset(v_bs_x27_705_, v_i_698_, v___x_707_);
v_i_698_ = v___x_709_;
v_bs_699_ = v___x_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___boxed(lean_object* v_s_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_bs_715_){
_start:
{
size_t v_sz_boxed_716_; size_t v_i_boxed_717_; lean_object* v_res_718_; 
v_sz_boxed_716_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_717_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_712_, v_sz_boxed_716_, v_i_boxed_717_, v_bs_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(lean_object* v_s_719_, size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_723_ == 0)
{
lean_dec_ref(v_s_719_);
return v_bs_722_;
}
else
{
lean_object* v_v_724_; lean_object* v___x_725_; lean_object* v_bs_x27_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v_v_724_ = lean_array_uget(v_bs_722_, v_i_721_);
v___x_725_ = lean_unsigned_to_nat(0u);
v_bs_x27_726_ = lean_array_uset(v_bs_722_, v_i_721_, v___x_725_);
lean_inc_ref(v_s_719_);
v___x_727_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_719_, v_v_724_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_721_, v___x_728_);
v___x_730_ = lean_array_uset(v_bs_x27_726_, v_i_721_, v___x_727_);
v_i_721_ = v___x_729_;
v_bs_722_ = v___x_730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(lean_object* v_s_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_object* v_cs_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_744_; 
v_cs_734_ = lean_ctor_get(v_x_733_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_736_ = v_x_733_;
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_cs_734_);
lean_dec(v_x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_sz_738_ = lean_array_size(v_cs_734_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_732_, v_sz_738_, v___x_739_, v_cs_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_vs_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_755_; 
v_vs_745_ = lean_ctor_get(v_x_733_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_755_ == 0)
{
v___x_747_ = v_x_733_;
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_vs_745_);
lean_dec(v_x_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
size_t v_sz_749_; size_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v_sz_749_ = lean_array_size(v_vs_745_);
v___x_750_ = ((size_t)0ULL);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_732_, v_sz_749_, v___x_750_, v_vs_745_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4___boxed(lean_object* v_s_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_bs_759_){
_start:
{
size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_sz_boxed_760_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_756_, v_sz_boxed_760_, v_i_boxed_761_, v_bs_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(lean_object* v_s_763_, lean_object* v_t_764_){
_start:
{
lean_object* v_root_765_; lean_object* v_tail_766_; lean_object* v_size_767_; size_t v_shift_768_; lean_object* v_tailOff_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_780_; 
v_root_765_ = lean_ctor_get(v_t_764_, 0);
v_tail_766_ = lean_ctor_get(v_t_764_, 1);
v_size_767_ = lean_ctor_get(v_t_764_, 2);
v_shift_768_ = lean_ctor_get_usize(v_t_764_, 4);
v_tailOff_769_ = lean_ctor_get(v_t_764_, 3);
v_isSharedCheck_780_ = !lean_is_exclusive(v_t_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_771_ = v_t_764_;
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_tailOff_769_);
lean_inc(v_size_767_);
lean_inc(v_tail_766_);
lean_inc(v_root_765_);
lean_dec(v_t_764_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_inc_ref(v_s_763_);
v___x_773_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_763_, v_root_765_);
v_sz_774_ = lean_array_size(v_tail_766_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_763_, v_sz_774_, v___x_775_, v_tail_766_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_size_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_tailOff_769_);
lean_ctor_set_usize(v_reuseFailAlloc_779_, 4, v_shift_768_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0(void){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0(lean_object* v_s_784_, lean_object* v_trees_785_, uint8_t v_enabled_786_, lean_object* v_assignment_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1);
v___x_790_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(v_s_784_, v_trees_785_);
v___x_791_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_791_, 0, v_assignment_787_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3, v_enabled_786_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed(lean_object* v_s_792_, lean_object* v_trees_793_, lean_object* v_enabled_794_, lean_object* v_assignment_795_, lean_object* v_x_796_){
_start:
{
uint8_t v_enabled_boxed_797_; lean_object* v_res_798_; 
v_enabled_boxed_797_ = lean_unbox(v_enabled_794_);
v_res_798_ = l_Lean_Elab_InfoState_substituteLazy___lam__0(v_s_792_, v_trees_793_, v_enabled_boxed_797_, v_assignment_795_, v_x_796_);
lean_dec(v_x_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0(lean_object* v_f_799_, lean_object* v_x1_800_, lean_object* v_x2_801_, lean_object* v_x3_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = lean_apply_3(v_f_799_, v_x1_800_, v_x2_801_, v_x3_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_f_804_, lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_i_807_, lean_object* v_acc_808_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_array_get_size(v_keys_805_);
v___x_810_ = lean_nat_dec_lt(v_i_807_, v___x_809_);
if (v___x_810_ == 0)
{
lean_dec(v_i_807_);
lean_dec(v_f_804_);
return v_acc_808_;
}
else
{
lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_k_811_ = lean_array_fget_borrowed(v_keys_805_, v_i_807_);
v_v_812_ = lean_array_fget_borrowed(v_vals_806_, v_i_807_);
lean_inc(v_f_804_);
lean_inc(v_v_812_);
lean_inc(v_k_811_);
v___x_813_ = lean_apply_3(v_f_804_, v_acc_808_, v_k_811_, v_v_812_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_i_807_, v___x_814_);
lean_dec(v_i_807_);
v_i_807_ = v___x_815_;
v_acc_808_ = v___x_813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_f_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_i_820_, lean_object* v_acc_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_817_, v_keys_818_, v_vals_819_, v_i_820_, v_acc_821_);
lean_dec_ref(v_vals_819_);
lean_dec_ref(v_keys_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_f_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v_es_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_es_826_ = lean_ctor_get(v_x_824_, 0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get_size(v_es_826_);
v___x_829_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_f_823_);
return v_x_825_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_le(v___x_828_, v___x_828_);
if (v___x_830_ == 0)
{
if (v___x_829_ == 0)
{
lean_dec(v_f_823_);
return v_x_825_;
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_828_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_823_, v_es_826_, v___x_831_, v___x_832_, v_x_825_);
return v___x_833_;
}
}
else
{
size_t v___x_834_; size_t v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((size_t)0ULL);
v___x_835_ = lean_usize_of_nat(v___x_828_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_823_, v_es_826_, v___x_834_, v___x_835_, v_x_825_);
return v___x_836_;
}
}
}
else
{
lean_object* v_ks_837_; lean_object* v_vs_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_ks_837_ = lean_ctor_get(v_x_824_, 0);
v_vs_838_ = lean_ctor_get(v_x_824_, 1);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_823_, v_ks_837_, v_vs_838_, v___x_839_, v_x_825_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(lean_object* v_f_841_, lean_object* v_as_842_, size_t v_i_843_, size_t v_stop_844_, lean_object* v_b_845_){
_start:
{
lean_object* v___y_847_; uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_eq(v_i_843_, v_stop_844_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_array_uget_borrowed(v_as_842_, v_i_843_);
switch(lean_obj_tag(v___x_852_))
{
case 0:
{
lean_object* v_key_853_; lean_object* v_val_854_; lean_object* v___x_855_; 
v_key_853_ = lean_ctor_get(v___x_852_, 0);
v_val_854_ = lean_ctor_get(v___x_852_, 1);
lean_inc(v_f_841_);
lean_inc(v_val_854_);
lean_inc(v_key_853_);
v___x_855_ = lean_apply_3(v_f_841_, v_b_845_, v_key_853_, v_val_854_);
v___y_847_ = v___x_855_;
goto v___jp_846_;
}
case 1:
{
lean_object* v_node_856_; lean_object* v___x_857_; 
v_node_856_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_f_841_);
v___x_857_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_841_, v_node_856_, v_b_845_);
v___y_847_ = v___x_857_;
goto v___jp_846_;
}
default: 
{
v___y_847_ = v_b_845_;
goto v___jp_846_;
}
}
}
else
{
lean_dec(v_f_841_);
return v_b_845_;
}
v___jp_846_:
{
size_t v___x_848_; size_t v___x_849_; 
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_add(v_i_843_, v___x_848_);
v_i_843_ = v___x_849_;
v_b_845_ = v___y_847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg___boxed(lean_object* v_f_858_, lean_object* v_as_859_, lean_object* v_i_860_, lean_object* v_stop_861_, lean_object* v_b_862_){
_start:
{
size_t v_i_boxed_863_; size_t v_stop_boxed_864_; lean_object* v_res_865_; 
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_stop_boxed_864_ = lean_unbox_usize(v_stop_861_);
lean_dec(v_stop_861_);
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_858_, v_as_859_, v_i_boxed_863_, v_stop_boxed_864_, v_b_862_);
lean_dec_ref(v_as_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_f_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_866_, v_x_867_, v_x_868_);
lean_dec_ref(v_x_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(lean_object* v_map_870_, lean_object* v_f_871_, lean_object* v_init_872_){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; 
v___f_873_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0), 4, 1);
lean_closure_set(v___f_873_, 0, v_f_871_);
v___x_874_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v___f_873_, v_map_870_, v_init_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___boxed(lean_object* v_map_875_, lean_object* v_f_876_, lean_object* v_init_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_875_, v_f_876_, v_init_877_);
lean_dec_ref(v_map_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0(lean_object* v_ps_879_, lean_object* v_k_880_, lean_object* v_v_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_k_880_);
lean_ctor_set(v___x_882_, 1, v_v_881_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_ps_879_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(lean_object* v_m_885_){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___f_886_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0));
v___x_887_ = lean_box(0);
v___x_888_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_m_885_, v___f_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___boxed(lean_object* v_m_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_889_);
lean_dec_ref(v_m_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_List_reverse___redArg(v_a_892_);
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_904_; 
v_head_894_ = lean_ctor_get(v_a_891_, 0);
v_tail_895_ = lean_ctor_get(v_a_891_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_904_ == 0)
{
v___x_897_ = v_a_891_;
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_tail_895_);
lean_inc(v_head_894_);
lean_dec(v_a_891_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_snd_899_; lean_object* v___x_901_; 
v_snd_899_ = lean_ctor_get(v_head_894_, 1);
lean_inc(v_snd_899_);
lean_dec(v_head_894_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v_a_892_);
lean_ctor_set(v___x_897_, 0, v_snd_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_snd_899_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_892_);
v___x_901_ = v_reuseFailAlloc_903_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
v_a_891_ = v_tail_895_;
v_a_892_ = v___x_901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object* v_s_905_){
_start:
{
uint8_t v_enabled_906_; lean_object* v_assignment_907_; lean_object* v_lazyAssignment_908_; lean_object* v_trees_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v_enabled_906_ = lean_ctor_get_uint8(v_s_905_, sizeof(void*)*3);
v_assignment_907_ = lean_ctor_get(v_s_905_, 0);
lean_inc_ref(v_assignment_907_);
v_lazyAssignment_908_ = lean_ctor_get(v_s_905_, 1);
lean_inc_ref(v_lazyAssignment_908_);
v_trees_909_ = lean_ctor_get(v_s_905_, 2);
lean_inc_ref(v_trees_909_);
v___x_910_ = lean_box(v_enabled_906_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed), 5, 4);
lean_closure_set(v___f_911_, 0, v_s_905_);
lean_closure_set(v___f_911_, 1, v_trees_909_);
lean_closure_set(v___f_911_, 2, v___x_910_);
lean_closure_set(v___f_911_, 3, v_assignment_907_);
v___x_912_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_lazyAssignment_908_);
lean_dec_ref(v_lazyAssignment_908_);
v___x_913_ = lean_box(0);
v___x_914_ = l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(v___x_912_, v___x_913_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = 0;
v___x_917_ = l_Task_mapList___redArg(v___f_911_, v___x_914_, v___x_915_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0(lean_object* v_00_u03b2_918_, lean_object* v_00_u03c3_919_, lean_object* v_pm_920_, lean_object* v_f_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_pm_920_, v_f_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(lean_object* v_00_u03b2_923_, lean_object* v_m_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___boxed(lean_object* v_00_u03b2_926_, lean_object* v_m_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(v_00_u03b2_926_, v_m_927_);
lean_dec_ref(v_m_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0___redArg(lean_object* v_pm_929_, lean_object* v_f_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_930_, v_pm_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0(lean_object* v_00_u03b2_932_, lean_object* v_00_u03c3_933_, lean_object* v_pm_934_, lean_object* v_f_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_935_, v_pm_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(lean_object* v_00_u03c3_937_, lean_object* v_00_u03b2_938_, lean_object* v_map_939_, lean_object* v_f_940_, lean_object* v_init_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_939_, v_f_940_, v_init_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___boxed(lean_object* v_00_u03c3_943_, lean_object* v_00_u03b2_944_, lean_object* v_map_945_, lean_object* v_f_946_, lean_object* v_init_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(v_00_u03c3_943_, v_00_u03b2_944_, v_map_945_, v_f_946_, v_init_947_);
lean_dec_ref(v_map_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_00_u03c3_951_, lean_object* v_f_952_, lean_object* v_n_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_952_, v_n_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(lean_object* v_map_955_, lean_object* v_f_956_, lean_object* v_init_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_956_, v_map_955_, v_init_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_map_959_, lean_object* v_f_960_, lean_object* v_init_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(v_map_959_, v_f_960_, v_init_961_);
lean_dec_ref(v_map_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_963_, lean_object* v_00_u03b2_964_, lean_object* v_map_965_, lean_object* v_f_966_, lean_object* v_init_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_966_, v_map_965_, v_init_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_969_, lean_object* v_00_u03b2_970_, lean_object* v_map_971_, lean_object* v_f_972_, lean_object* v_init_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(v_00_u03c3_969_, v_00_u03b2_970_, v_map_971_, v_f_972_, v_init_973_);
lean_dec_ref(v_map_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_00_u03c3_977_, lean_object* v_f_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_bs_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_978_, v_sz_979_, v_i_980_, v_bs_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_00_u03c3_985_, lean_object* v_f_986_, lean_object* v_sz_987_, lean_object* v_i_988_, lean_object* v_bs_989_){
_start:
{
size_t v_sz_boxed_990_; size_t v_i_boxed_991_; lean_object* v_res_992_; 
v_sz_boxed_990_ = lean_unbox_usize(v_sz_987_);
lean_dec(v_sz_987_);
v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_983_, v_00_u03b2_984_, v_00_u03c3_985_, v_f_986_, v_sz_boxed_990_, v_i_boxed_991_, v_bs_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_f_995_, lean_object* v_as_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_995_, v_as_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_f_1000_, lean_object* v_as_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_998_, v_00_u03b2_999_, v_f_1000_, v_as_1001_);
lean_dec_ref(v_as_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_1003_, lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_f_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1006_, v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03c3_1010_, lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_f_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(v_00_u03c3_1010_, v_00_u03b1_1011_, v_00_u03b2_1012_, v_f_1013_, v_x_1014_, v_x_1015_);
lean_dec_ref(v_x_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_f_1019_, lean_object* v_as_1020_, lean_object* v_i_1021_, lean_object* v_acc_1022_, lean_object* v_hle_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_1019_, v_as_1020_, v_i_1021_, v_acc_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_f_1027_, lean_object* v_as_1028_, lean_object* v_i_1029_, lean_object* v_acc_1030_, lean_object* v_hle_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_1025_, v_00_u03b2_1026_, v_f_1027_, v_as_1028_, v_i_1029_, v_acc_1030_, v_hle_1031_);
lean_dec_ref(v_as_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_00_u03c3_1035_, lean_object* v_f_1036_, lean_object* v_as_1037_, size_t v_i_1038_, size_t v_stop_1039_, lean_object* v_b_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_1036_, v_as_1037_, v_i_1038_, v_stop_1039_, v_b_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_00_u03c3_1044_, lean_object* v_f_1045_, lean_object* v_as_1046_, lean_object* v_i_1047_, lean_object* v_stop_1048_, lean_object* v_b_1049_){
_start:
{
size_t v_i_boxed_1050_; size_t v_stop_boxed_1051_; lean_object* v_res_1052_; 
v_i_boxed_1050_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_stop_boxed_1051_ = lean_unbox_usize(v_stop_1048_);
lean_dec(v_stop_1048_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(v_00_u03b1_1042_, v_00_u03b2_1043_, v_00_u03c3_1044_, v_f_1045_, v_as_1046_, v_i_boxed_1050_, v_stop_boxed_1051_, v_b_1049_);
lean_dec_ref(v_as_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03c3_1053_, lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_f_1056_, lean_object* v_keys_1057_, lean_object* v_vals_1058_, lean_object* v_heq_1059_, lean_object* v_i_1060_, lean_object* v_acc_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_1056_, v_keys_1057_, v_vals_1058_, v_i_1060_, v_acc_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03c3_1063_, lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_f_1066_, lean_object* v_keys_1067_, lean_object* v_vals_1068_, lean_object* v_heq_1069_, lean_object* v_i_1070_, lean_object* v_acc_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(v_00_u03c3_1063_, v_00_u03b1_1064_, v_00_u03b2_1065_, v_f_1066_, v_keys_1067_, v_vals_1068_, v_heq_1069_, v_i_1070_, v_acc_1071_);
lean_dec_ref(v_vals_1068_);
lean_dec_ref(v_keys_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_1073_, lean_object* v_opt_1074_){
_start:
{
lean_object* v_name_1075_; lean_object* v_defValue_1076_; lean_object* v_map_1077_; lean_object* v___x_1078_; 
v_name_1075_ = lean_ctor_get(v_opt_1074_, 0);
v_defValue_1076_ = lean_ctor_get(v_opt_1074_, 1);
v_map_1077_ = lean_ctor_get(v_opts_1073_, 0);
v___x_1078_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1077_, v_name_1075_);
if (lean_obj_tag(v___x_1078_) == 0)
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_unbox(v_defValue_1076_);
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; 
v_val_1080_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v___x_1078_, 1);
if (lean_obj_tag(v_val_1080_) == 1)
{
uint8_t v_v_1081_; 
v_v_1081_ = lean_ctor_get_uint8(v_val_1080_, 0);
lean_dec_ref_known(v_val_1080_, 0);
return v_v_1081_;
}
else
{
uint8_t v___x_1082_; 
lean_dec(v_val_1080_);
v___x_1082_ = lean_unbox(v_defValue_1076_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_1083_, lean_object* v_opt_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_1083_, v_opt_1084_);
lean_dec_ref(v_opt_1084_);
lean_dec_ref(v_opts_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object* v_opts_1087_, lean_object* v_opt_1088_){
_start:
{
lean_object* v_name_1089_; lean_object* v_defValue_1090_; lean_object* v_map_1091_; lean_object* v___x_1092_; 
v_name_1089_ = lean_ctor_get(v_opt_1088_, 0);
v_defValue_1090_ = lean_ctor_get(v_opt_1088_, 1);
v_map_1091_ = lean_ctor_get(v_opts_1087_, 0);
v___x_1092_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1091_, v_name_1089_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_inc(v_defValue_1090_);
return v_defValue_1090_;
}
else
{
lean_object* v_val_1093_; 
v_val_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v___x_1092_, 1);
if (lean_obj_tag(v_val_1093_) == 3)
{
lean_object* v_v_1094_; 
v_v_1094_ = lean_ctor_get(v_val_1093_, 0);
lean_inc(v_v_1094_);
lean_dec_ref_known(v_val_1093_, 1);
return v_v_1094_;
}
else
{
lean_dec(v_val_1093_);
lean_inc(v_defValue_1090_);
return v_defValue_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object* v_opts_1095_, lean_object* v_opt_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_opts_1095_, v_opt_1096_);
lean_dec_ref(v_opt_1096_);
lean_dec_ref(v_opts_1095_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_unsigned_to_nat(32u);
v___x_1099_ = lean_mk_empty_array_with_capacity(v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
size_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1101_ = ((size_t)5ULL);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_unsigned_to_nat(32u);
v___x_1104_ = lean_mk_empty_array_with_capacity(v___x_1103_);
v___x_1105_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0);
v___x_1106_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
lean_ctor_set(v___x_1106_, 2, v___x_1102_);
lean_ctor_set(v___x_1106_, 3, v___x_1102_);
lean_ctor_set_usize(v___x_1106_, 4, v___x_1101_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = l_Lean_NameSet_empty;
v___x_1113_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
lean_ctor_set(v___x_1114_, 2, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = l_Lean_firstFrontendMacroScope;
v___x_1117_ = lean_nat_add(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_1122_; uint64_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1123_ = 0ULL;
v___x_1124_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set_uint64(v___x_1124_, sizeof(void*)*1, v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1126_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1127_ = 1;
v___x_1128_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1126_);
lean_ctor_set(v___x_1128_, 2, v___x_1125_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*3, v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l_Lean_Options_empty;
v___x_1136_ = l_Lean_Core_getMaxHeartbeats(v___x_1135_);
return v___x_1136_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = l_Lean_diagnostics;
v___x_1138_ = l_Lean_Options_empty;
v___x_1139_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_maxRecDepth;
v___x_1141_ = l_Lean_Options_empty;
v___x_1142_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_a_1147_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_toCommandContextInfo_1154_; lean_object* v_env_1155_; lean_object* v_options_1156_; lean_object* v_currNamespace_1157_; lean_object* v_openDecls_1158_; lean_object* v_ngen_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v_env_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___y_1173_; lean_object* v___y_1174_; lean_object* v_fileName_1175_; lean_object* v_fileMap_1176_; lean_object* v_currRecDepth_1177_; lean_object* v_ref_1178_; lean_object* v_currNamespace_1179_; lean_object* v_openDecls_1180_; lean_object* v_initHeartbeats_1181_; lean_object* v_maxHeartbeats_1182_; lean_object* v_quotContext_1183_; lean_object* v_currMacroScope_1184_; lean_object* v_cancelTk_x3f_1185_; uint8_t v_suppressElabErrors_1186_; lean_object* v_inheritedTraceOptions_1187_; lean_object* v___y_1188_; uint8_t v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; uint8_t v___y_1246_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_env_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___y_1281_; lean_object* v___y_1282_; uint8_t v___y_1312_; uint8_t v___x_1332_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_1152_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_1153_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_1154_ = lean_ctor_get(v_info_1143_, 0);
lean_inc_ref(v_toCommandContextInfo_1154_);
lean_dec_ref(v_info_1143_);
v_env_1155_ = lean_ctor_get(v_toCommandContextInfo_1154_, 0);
lean_inc_ref(v_env_1155_);
v_options_1156_ = lean_ctor_get(v_toCommandContextInfo_1154_, 4);
lean_inc_ref(v_options_1156_);
v_currNamespace_1157_ = lean_ctor_get(v_toCommandContextInfo_1154_, 5);
lean_inc(v_currNamespace_1157_);
v_openDecls_1158_ = lean_ctor_get(v_toCommandContextInfo_1154_, 6);
lean_inc(v_openDecls_1158_);
v_ngen_1159_ = lean_ctor_get(v_toCommandContextInfo_1154_, 7);
lean_inc_ref(v_ngen_1159_);
lean_dec_ref(v_toCommandContextInfo_1154_);
v___x_1160_ = l_Lean_firstFrontendMacroScope;
v___x_1161_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_1162_ = 0;
v_env_1163_ = l_Lean_Environment_setExporting(v_env_1155_, v___x_1162_);
v___x_1164_ = lean_box(0);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7));
v___x_1166_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1167_ = 1;
v___x_1168_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_1170_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1170_, 0, v_env_1163_);
lean_ctor_set(v___x_1170_, 1, v___x_1161_);
lean_ctor_set(v___x_1170_, 2, v_ngen_1159_);
lean_ctor_set(v___x_1170_, 3, v___x_1165_);
lean_ctor_set(v___x_1170_, 4, v___x_1166_);
lean_ctor_set(v___x_1170_, 5, v___x_1151_);
lean_ctor_set(v___x_1170_, 6, v___x_1152_);
lean_ctor_set(v___x_1170_, 7, v___x_1168_);
lean_ctor_set(v___x_1170_, 8, v___x_1169_);
v___x_1171_ = lean_st_mk_ref(v___x_1170_);
v___x_1266_ = l_Lean_inheritedTraceOptions;
v___x_1267_ = lean_st_ref_get(v___x_1266_);
v___x_1268_ = lean_st_ref_get(v___x_1171_);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_1270_ = l_Lean_instInhabitedFileMap_default;
v___x_1271_ = l_Lean_Options_empty;
v___x_1272_ = lean_unsigned_to_nat(1000u);
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1276_, 0, v___x_1269_);
lean_ctor_set(v___x_1276_, 1, v___x_1270_);
lean_ctor_set(v___x_1276_, 2, v___x_1271_);
lean_ctor_set(v___x_1276_, 3, v___x_1150_);
lean_ctor_set(v___x_1276_, 4, v___x_1272_);
lean_ctor_set(v___x_1276_, 5, v___x_1273_);
lean_ctor_set(v___x_1276_, 6, v_currNamespace_1157_);
lean_ctor_set(v___x_1276_, 7, v_openDecls_1158_);
lean_ctor_set(v___x_1276_, 8, v___x_1153_);
lean_ctor_set(v___x_1276_, 9, v___x_1274_);
lean_ctor_set(v___x_1276_, 10, v___x_1164_);
lean_ctor_set(v___x_1276_, 11, v___x_1160_);
lean_ctor_set(v___x_1276_, 12, v___x_1275_);
lean_ctor_set(v___x_1276_, 13, v___x_1267_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*14, v___x_1162_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*14 + 1, v___x_1162_);
v_env_1277_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_env_1277_);
lean_dec(v___x_1268_);
v___x_1278_ = l_Lean_diagnostics;
v___x_1279_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_1332_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1277_);
lean_dec_ref(v_env_1277_);
if (v___x_1332_ == 0)
{
if (v___x_1279_ == 0)
{
lean_inc(v___x_1171_);
v___y_1281_ = v___x_1276_;
v___y_1282_ = v___x_1171_;
goto v___jp_1280_;
}
else
{
v___y_1312_ = v___x_1332_;
goto v___jp_1311_;
}
}
else
{
v___y_1312_ = v___x_1279_;
goto v___jp_1311_;
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_mk_io_user_error(v_a_1147_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
v___jp_1172_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_1156_, v___y_1174_);
v___x_1190_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1190_, 0, v_fileName_1175_);
lean_ctor_set(v___x_1190_, 1, v_fileMap_1176_);
lean_ctor_set(v___x_1190_, 2, v_options_1156_);
lean_ctor_set(v___x_1190_, 3, v_currRecDepth_1177_);
lean_ctor_set(v___x_1190_, 4, v___x_1189_);
lean_ctor_set(v___x_1190_, 5, v_ref_1178_);
lean_ctor_set(v___x_1190_, 6, v_currNamespace_1179_);
lean_ctor_set(v___x_1190_, 7, v_openDecls_1180_);
lean_ctor_set(v___x_1190_, 8, v_initHeartbeats_1181_);
lean_ctor_set(v___x_1190_, 9, v_maxHeartbeats_1182_);
lean_ctor_set(v___x_1190_, 10, v_quotContext_1183_);
lean_ctor_set(v___x_1190_, 11, v_currMacroScope_1184_);
lean_ctor_set(v___x_1190_, 12, v_cancelTk_x3f_1185_);
lean_ctor_set(v___x_1190_, 13, v_inheritedTraceOptions_1187_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*14, v___y_1173_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*14 + 1, v_suppressElabErrors_1186_);
v___x_1191_ = lean_apply_3(v_x_1144_, v___x_1190_, v___y_1188_, lean_box(0));
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_st_ref_get(v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1196_);
if (v_isShared_1195_ == 0)
{
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1192_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v___x_1171_);
v_a_1201_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1203_ = v___x_1191_;
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
if (lean_obj_tag(v_a_1201_) == 0)
{
lean_object* v_msg_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v_msg_1205_ = lean_ctor_get(v_a_1201_, 1);
lean_inc_ref(v_msg_1205_);
lean_dec_ref_known(v_a_1201_, 2);
v___x_1206_ = l_Lean_MessageData_toString(v_msg_1205_);
v___x_1207_ = lean_mk_io_user_error(v___x_1206_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
lean_object* v_id_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1203_);
v_id_1211_ = lean_ctor_get(v_a_1201_, 0);
lean_inc(v_id_1211_);
lean_dec_ref_known(v_a_1201_, 2);
v___x_1212_ = l_Lean_InternalExceptionId_getName(v_id_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec(v_id_1211_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_1215_ = l_Lean_Name_toString(v_a_1213_, v___x_1167_);
v___x_1216_ = lean_string_append(v___x_1214_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v_a_1147_ = v___x_1216_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref_known(v___x_1212_, 1);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_1218_ = l_Nat_reprFast(v_id_1211_);
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
v_a_1147_ = v___x_1221_;
goto v___jp_1146_;
}
}
}
}
}
v___jp_1223_:
{
lean_object* v_fileName_1228_; lean_object* v_fileMap_1229_; lean_object* v_currRecDepth_1230_; lean_object* v_ref_1231_; lean_object* v_currNamespace_1232_; lean_object* v_openDecls_1233_; lean_object* v_initHeartbeats_1234_; lean_object* v_maxHeartbeats_1235_; lean_object* v_quotContext_1236_; lean_object* v_currMacroScope_1237_; lean_object* v_cancelTk_x3f_1238_; uint8_t v_suppressElabErrors_1239_; lean_object* v_inheritedTraceOptions_1240_; 
v_fileName_1228_ = lean_ctor_get(v___y_1226_, 0);
lean_inc_ref(v_fileName_1228_);
v_fileMap_1229_ = lean_ctor_get(v___y_1226_, 1);
lean_inc_ref(v_fileMap_1229_);
v_currRecDepth_1230_ = lean_ctor_get(v___y_1226_, 3);
lean_inc(v_currRecDepth_1230_);
v_ref_1231_ = lean_ctor_get(v___y_1226_, 5);
lean_inc(v_ref_1231_);
v_currNamespace_1232_ = lean_ctor_get(v___y_1226_, 6);
lean_inc(v_currNamespace_1232_);
v_openDecls_1233_ = lean_ctor_get(v___y_1226_, 7);
lean_inc(v_openDecls_1233_);
v_initHeartbeats_1234_ = lean_ctor_get(v___y_1226_, 8);
lean_inc(v_initHeartbeats_1234_);
v_maxHeartbeats_1235_ = lean_ctor_get(v___y_1226_, 9);
lean_inc(v_maxHeartbeats_1235_);
v_quotContext_1236_ = lean_ctor_get(v___y_1226_, 10);
lean_inc(v_quotContext_1236_);
v_currMacroScope_1237_ = lean_ctor_get(v___y_1226_, 11);
lean_inc(v_currMacroScope_1237_);
v_cancelTk_x3f_1238_ = lean_ctor_get(v___y_1226_, 12);
lean_inc(v_cancelTk_x3f_1238_);
v_suppressElabErrors_1239_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1240_ = lean_ctor_get(v___y_1226_, 13);
lean_inc_ref(v_inheritedTraceOptions_1240_);
lean_dec_ref(v___y_1226_);
v___y_1173_ = v___y_1224_;
v___y_1174_ = v___y_1225_;
v_fileName_1175_ = v_fileName_1228_;
v_fileMap_1176_ = v_fileMap_1229_;
v_currRecDepth_1177_ = v_currRecDepth_1230_;
v_ref_1178_ = v_ref_1231_;
v_currNamespace_1179_ = v_currNamespace_1232_;
v_openDecls_1180_ = v_openDecls_1233_;
v_initHeartbeats_1181_ = v_initHeartbeats_1234_;
v_maxHeartbeats_1182_ = v_maxHeartbeats_1235_;
v_quotContext_1183_ = v_quotContext_1236_;
v_currMacroScope_1184_ = v_currMacroScope_1237_;
v_cancelTk_x3f_1185_ = v_cancelTk_x3f_1238_;
v_suppressElabErrors_1186_ = v_suppressElabErrors_1239_;
v_inheritedTraceOptions_1187_ = v_inheritedTraceOptions_1240_;
v___y_1188_ = v___y_1227_;
goto v___jp_1172_;
}
v___jp_1241_:
{
if (v___y_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v_env_1248_; lean_object* v_nextMacroScope_1249_; lean_object* v_ngen_1250_; lean_object* v_auxDeclNGen_1251_; lean_object* v_traceState_1252_; lean_object* v_messages_1253_; lean_object* v_infoState_1254_; lean_object* v_snapshotTasks_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v___x_1247_ = lean_st_ref_take(v___y_1244_);
v_env_1248_ = lean_ctor_get(v___x_1247_, 0);
v_nextMacroScope_1249_ = lean_ctor_get(v___x_1247_, 1);
v_ngen_1250_ = lean_ctor_get(v___x_1247_, 2);
v_auxDeclNGen_1251_ = lean_ctor_get(v___x_1247_, 3);
v_traceState_1252_ = lean_ctor_get(v___x_1247_, 4);
v_messages_1253_ = lean_ctor_get(v___x_1247_, 6);
v_infoState_1254_ = lean_ctor_get(v___x_1247_, 7);
v_snapshotTasks_1255_ = lean_ctor_get(v___x_1247_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1247_, 5);
lean_dec(v_unused_1265_);
v___x_1257_ = v___x_1247_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snapshotTasks_1255_);
lean_inc(v_infoState_1254_);
lean_inc(v_messages_1253_);
lean_inc(v_traceState_1252_);
lean_inc(v_auxDeclNGen_1251_);
lean_inc(v_ngen_1250_);
lean_inc(v_nextMacroScope_1249_);
lean_inc(v_env_1248_);
lean_dec(v___x_1247_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_Kernel_enableDiag(v_env_1248_, v___y_1243_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 5, v___x_1151_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1249_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1250_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1251_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1252_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_messages_1253_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_infoState_1254_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_snapshotTasks_1255_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_st_ref_set(v___y_1244_, v___x_1261_);
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1242_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1244_;
goto v___jp_1223_;
}
}
}
else
{
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1242_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1244_;
goto v___jp_1223_;
}
}
v___jp_1280_:
{
lean_object* v___x_1283_; lean_object* v_fileName_1284_; lean_object* v_fileMap_1285_; lean_object* v_currRecDepth_1286_; lean_object* v_ref_1287_; lean_object* v_currNamespace_1288_; lean_object* v_openDecls_1289_; lean_object* v_initHeartbeats_1290_; lean_object* v_maxHeartbeats_1291_; lean_object* v_quotContext_1292_; lean_object* v_currMacroScope_1293_; lean_object* v_cancelTk_x3f_1294_; uint8_t v_suppressElabErrors_1295_; lean_object* v_inheritedTraceOptions_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1308_; 
v___x_1283_ = lean_st_ref_get(v___y_1282_);
v_fileName_1284_ = lean_ctor_get(v___y_1281_, 0);
v_fileMap_1285_ = lean_ctor_get(v___y_1281_, 1);
v_currRecDepth_1286_ = lean_ctor_get(v___y_1281_, 3);
v_ref_1287_ = lean_ctor_get(v___y_1281_, 5);
v_currNamespace_1288_ = lean_ctor_get(v___y_1281_, 6);
v_openDecls_1289_ = lean_ctor_get(v___y_1281_, 7);
v_initHeartbeats_1290_ = lean_ctor_get(v___y_1281_, 8);
v_maxHeartbeats_1291_ = lean_ctor_get(v___y_1281_, 9);
v_quotContext_1292_ = lean_ctor_get(v___y_1281_, 10);
v_currMacroScope_1293_ = lean_ctor_get(v___y_1281_, 11);
v_cancelTk_x3f_1294_ = lean_ctor_get(v___y_1281_, 12);
v_suppressElabErrors_1295_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1296_ = lean_ctor_get(v___y_1281_, 13);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; lean_object* v_unused_1310_; 
v_unused_1309_ = lean_ctor_get(v___y_1281_, 4);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v___y_1281_, 2);
lean_dec(v_unused_1310_);
v___x_1298_ = v___y_1281_;
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_inheritedTraceOptions_1296_);
lean_inc(v_cancelTk_x3f_1294_);
lean_inc(v_currMacroScope_1293_);
lean_inc(v_quotContext_1292_);
lean_inc(v_maxHeartbeats_1291_);
lean_inc(v_initHeartbeats_1290_);
lean_inc(v_openDecls_1289_);
lean_inc(v_currNamespace_1288_);
lean_inc(v_ref_1287_);
lean_inc(v_currRecDepth_1286_);
lean_inc(v_fileMap_1285_);
lean_inc(v_fileName_1284_);
lean_dec(v___y_1281_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_env_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v_env_1300_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_env_1300_);
lean_dec(v___x_1283_);
v___x_1301_ = l_Lean_maxRecDepth;
v___x_1302_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_1296_);
lean_inc(v_cancelTk_x3f_1294_);
lean_inc(v_currMacroScope_1293_);
lean_inc(v_quotContext_1292_);
lean_inc(v_maxHeartbeats_1291_);
lean_inc(v_initHeartbeats_1290_);
lean_inc(v_openDecls_1289_);
lean_inc(v_currNamespace_1288_);
lean_inc(v_ref_1287_);
lean_inc(v_currRecDepth_1286_);
lean_inc_ref(v_fileMap_1285_);
lean_inc_ref(v_fileName_1284_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1302_);
lean_ctor_set(v___x_1298_, 2, v___x_1271_);
v___x_1304_ = v___x_1298_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_fileName_1284_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_fileMap_1285_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_currRecDepth_1286_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1307_, 5, v_ref_1287_);
lean_ctor_set(v_reuseFailAlloc_1307_, 6, v_currNamespace_1288_);
lean_ctor_set(v_reuseFailAlloc_1307_, 7, v_openDecls_1289_);
lean_ctor_set(v_reuseFailAlloc_1307_, 8, v_initHeartbeats_1290_);
lean_ctor_set(v_reuseFailAlloc_1307_, 9, v_maxHeartbeats_1291_);
lean_ctor_set(v_reuseFailAlloc_1307_, 10, v_quotContext_1292_);
lean_ctor_set(v_reuseFailAlloc_1307_, 11, v_currMacroScope_1293_);
lean_ctor_set(v_reuseFailAlloc_1307_, 12, v_cancelTk_x3f_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 13, v_inheritedTraceOptions_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*14 + 1, v_suppressElabErrors_1295_);
v___x_1304_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
uint8_t v___x_1305_; uint8_t v___x_1306_; 
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*14, v___x_1279_);
v___x_1305_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_1156_, v___x_1278_);
v___x_1306_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1300_);
lean_dec_ref(v_env_1300_);
if (v___x_1306_ == 0)
{
if (v___x_1305_ == 0)
{
lean_dec_ref(v___x_1304_);
v___y_1173_ = v___x_1305_;
v___y_1174_ = v___x_1301_;
v_fileName_1175_ = v_fileName_1284_;
v_fileMap_1176_ = v_fileMap_1285_;
v_currRecDepth_1177_ = v_currRecDepth_1286_;
v_ref_1178_ = v_ref_1287_;
v_currNamespace_1179_ = v_currNamespace_1288_;
v_openDecls_1180_ = v_openDecls_1289_;
v_initHeartbeats_1181_ = v_initHeartbeats_1290_;
v_maxHeartbeats_1182_ = v_maxHeartbeats_1291_;
v_quotContext_1183_ = v_quotContext_1292_;
v_currMacroScope_1184_ = v_currMacroScope_1293_;
v_cancelTk_x3f_1185_ = v_cancelTk_x3f_1294_;
v_suppressElabErrors_1186_ = v_suppressElabErrors_1295_;
v_inheritedTraceOptions_1187_ = v_inheritedTraceOptions_1296_;
v___y_1188_ = v___y_1282_;
goto v___jp_1172_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1296_);
lean_dec(v_cancelTk_x3f_1294_);
lean_dec(v_currMacroScope_1293_);
lean_dec(v_quotContext_1292_);
lean_dec(v_maxHeartbeats_1291_);
lean_dec(v_initHeartbeats_1290_);
lean_dec(v_openDecls_1289_);
lean_dec(v_currNamespace_1288_);
lean_dec(v_ref_1287_);
lean_dec(v_currRecDepth_1286_);
lean_dec_ref(v_fileMap_1285_);
lean_dec_ref(v_fileName_1284_);
v___y_1242_ = v___x_1301_;
v___y_1243_ = v___x_1305_;
v___y_1244_ = v___y_1282_;
v___y_1245_ = v___x_1304_;
v___y_1246_ = v___x_1306_;
goto v___jp_1241_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1296_);
lean_dec(v_cancelTk_x3f_1294_);
lean_dec(v_currMacroScope_1293_);
lean_dec(v_quotContext_1292_);
lean_dec(v_maxHeartbeats_1291_);
lean_dec(v_initHeartbeats_1290_);
lean_dec(v_openDecls_1289_);
lean_dec(v_currNamespace_1288_);
lean_dec(v_ref_1287_);
lean_dec(v_currRecDepth_1286_);
lean_dec_ref(v_fileMap_1285_);
lean_dec_ref(v_fileName_1284_);
v___y_1242_ = v___x_1301_;
v___y_1243_ = v___x_1305_;
v___y_1244_ = v___y_1282_;
v___y_1245_ = v___x_1304_;
v___y_1246_ = v___x_1305_;
goto v___jp_1241_;
}
}
}
}
v___jp_1311_:
{
if (v___y_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v_env_1314_; lean_object* v_nextMacroScope_1315_; lean_object* v_ngen_1316_; lean_object* v_auxDeclNGen_1317_; lean_object* v_traceState_1318_; lean_object* v_messages_1319_; lean_object* v_infoState_1320_; lean_object* v_snapshotTasks_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1330_; 
v___x_1313_ = lean_st_ref_take(v___x_1171_);
v_env_1314_ = lean_ctor_get(v___x_1313_, 0);
v_nextMacroScope_1315_ = lean_ctor_get(v___x_1313_, 1);
v_ngen_1316_ = lean_ctor_get(v___x_1313_, 2);
v_auxDeclNGen_1317_ = lean_ctor_get(v___x_1313_, 3);
v_traceState_1318_ = lean_ctor_get(v___x_1313_, 4);
v_messages_1319_ = lean_ctor_get(v___x_1313_, 6);
v_infoState_1320_ = lean_ctor_get(v___x_1313_, 7);
v_snapshotTasks_1321_ = lean_ctor_get(v___x_1313_, 8);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v___x_1313_, 5);
lean_dec(v_unused_1331_);
v___x_1323_ = v___x_1313_;
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_snapshotTasks_1321_);
lean_inc(v_infoState_1320_);
lean_inc(v_messages_1319_);
lean_inc(v_traceState_1318_);
lean_inc(v_auxDeclNGen_1317_);
lean_inc(v_ngen_1316_);
lean_inc(v_nextMacroScope_1315_);
lean_inc(v_env_1314_);
lean_dec(v___x_1313_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = l_Lean_Kernel_enableDiag(v_env_1314_, v___x_1279_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 5, v___x_1151_);
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_nextMacroScope_1315_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_ngen_1316_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v_auxDeclNGen_1317_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_traceState_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 5, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1329_, 6, v_messages_1319_);
lean_ctor_set(v_reuseFailAlloc_1329_, 7, v_infoState_1320_);
lean_ctor_set(v_reuseFailAlloc_1329_, 8, v_snapshotTasks_1321_);
v___x_1327_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_st_ref_set(v___x_1171_, v___x_1327_);
lean_inc(v___x_1171_);
v___y_1281_ = v___x_1276_;
v___y_1282_ = v___x_1171_;
goto v___jp_1280_;
}
}
}
else
{
lean_inc(v___x_1171_);
v___y_1281_ = v___x_1276_;
v___y_1282_ = v___x_1171_;
goto v___jp_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_1333_, lean_object* v_x_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1333_, v_x_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_1337_, lean_object* v_info_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1338_, v_x_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_info_1343_, lean_object* v_x_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_1342_, v_info_1343_, v_x_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_1347_, lean_object* v_x_1348_, lean_object* v___x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_st_mk_ref(v___x_1347_);
lean_inc(v___x_1353_);
v___x_1354_ = lean_apply_5(v_x_1348_, v___x_1349_, v___x_1353_, v___y_1350_, v___y_1351_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1364_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_st_ref_get(v___x_1353_);
lean_dec(v___x_1353_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1355_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1360_);
v___x_1362_ = v___x_1357_;
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
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v___x_1353_);
v_a_1365_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1354_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1354_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_1373_, lean_object* v_x_1374_, lean_object* v___x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_1373_, v_x_1374_, v___x_1375_, v___y_1376_, v___y_1377_);
return v_res_1379_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1386_; uint64_t v___x_1387_; 
v___x_1386_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_1389_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1390_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set_uint64(v___x_1390_, sizeof(void*)*1, v___x_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
lean_ctor_set(v___x_1397_, 3, v___x_1396_);
lean_ctor_set(v___x_1397_, 4, v___x_1396_);
lean_ctor_set(v___x_1397_, 5, v___x_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_unsigned_to_nat(32u);
v___x_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((size_t)5ULL);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_unsigned_to_nat(32u);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_1406_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1402_);
lean_ctor_set(v___x_1406_, 3, v___x_1402_);
lean_ctor_set_usize(v___x_1406_, 4, v___x_1401_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_ctor_set(v___x_1408_, 2, v___x_1407_);
lean_ctor_set(v___x_1408_, 3, v___x_1407_);
lean_ctor_set(v___x_1408_, 4, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_1409_, lean_object* v_lctx_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_toCommandContextInfo_1421_; lean_object* v_mctx_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; 
v___x_1413_ = lean_box(1);
v___x_1414_ = 0;
v___x_1415_ = 1;
v___x_1416_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1420_, 0, v___x_1416_);
lean_ctor_set(v___x_1420_, 1, v___x_1413_);
lean_ctor_set(v___x_1420_, 2, v_lctx_1410_);
lean_ctor_set(v___x_1420_, 3, v___x_1418_);
lean_ctor_set(v___x_1420_, 4, v___x_1419_);
lean_ctor_set(v___x_1420_, 5, v___x_1417_);
lean_ctor_set(v___x_1420_, 6, v___x_1419_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*7, v___x_1414_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*7 + 1, v___x_1414_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*7 + 2, v___x_1414_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*7 + 3, v___x_1415_);
v_toCommandContextInfo_1421_ = lean_ctor_get(v_info_1409_, 0);
v_mctx_1422_ = lean_ctor_get(v_toCommandContextInfo_1421_, 3);
v___x_1423_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_1424_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_1425_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_1422_);
v___x_1426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1426_, 0, v_mctx_1422_);
lean_ctor_set(v___x_1426_, 1, v___x_1423_);
lean_ctor_set(v___x_1426_, 2, v___x_1413_);
lean_ctor_set(v___x_1426_, 3, v___x_1424_);
lean_ctor_set(v___x_1426_, 4, v___x_1425_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1427_, 0, v___x_1426_);
lean_closure_set(v___f_1427_, 1, v_x_1411_);
lean_closure_set(v___f_1427_, 2, v___x_1420_);
v___x_1428_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1409_, v___f_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v___x_1435_; 
v_fst_1433_ = lean_ctor_get(v_a_1429_, 0);
lean_inc(v_fst_1433_);
lean_dec(v_a_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v_fst_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_fst_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1428_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1428_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_1446_, lean_object* v_lctx_1447_, lean_object* v_x_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1446_, v_lctx_1447_, v_x_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_1451_, lean_object* v_info_1452_, lean_object* v_lctx_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1452_, v_lctx_1453_, v_x_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_info_1458_, lean_object* v_lctx_1459_, lean_object* v_x_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_1457_, v_info_1458_, v_lctx_1459_, v_x_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_1463_, lean_object* v_lctx_1464_){
_start:
{
lean_object* v_toCommandContextInfo_1465_; lean_object* v_env_1466_; lean_object* v_mctx_1467_; lean_object* v_options_1468_; lean_object* v_currNamespace_1469_; lean_object* v_openDecls_1470_; lean_object* v___x_1471_; 
v_toCommandContextInfo_1465_ = lean_ctor_get(v_info_1463_, 0);
v_env_1466_ = lean_ctor_get(v_toCommandContextInfo_1465_, 0);
v_mctx_1467_ = lean_ctor_get(v_toCommandContextInfo_1465_, 3);
v_options_1468_ = lean_ctor_get(v_toCommandContextInfo_1465_, 4);
v_currNamespace_1469_ = lean_ctor_get(v_toCommandContextInfo_1465_, 5);
v_openDecls_1470_ = lean_ctor_get(v_toCommandContextInfo_1465_, 6);
lean_inc(v_openDecls_1470_);
lean_inc(v_currNamespace_1469_);
lean_inc_ref(v_options_1468_);
lean_inc_ref(v_mctx_1467_);
lean_inc_ref(v_env_1466_);
v___x_1471_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1471_, 0, v_env_1466_);
lean_ctor_set(v___x_1471_, 1, v_mctx_1467_);
lean_ctor_set(v___x_1471_, 2, v_lctx_1464_);
lean_ctor_set(v___x_1471_, 3, v_options_1468_);
lean_ctor_set(v___x_1471_, 4, v_currNamespace_1469_);
lean_ctor_set(v___x_1471_, 5, v_openDecls_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_1472_, lean_object* v_lctx_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1472_, v_lctx_1473_);
lean_dec_ref(v_info_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_1475_, lean_object* v_lctx_1476_, lean_object* v_stx_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1475_, v_lctx_1476_);
v___x_1480_ = l_Lean_ppTerm(v___x_1479_, v_stx_1477_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_1482_, lean_object* v_lctx_1483_, lean_object* v_stx_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_1482_, v_lctx_1483_, v_stx_1484_);
lean_dec_ref(v_info_1482_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_1502_, lean_object* v_pos_1503_, lean_object* v_info_1504_){
_start:
{
lean_object* v_toCommandContextInfo_1505_; lean_object* v_fileMap_1506_; lean_object* v___x_1507_; lean_object* v_line_1508_; lean_object* v_column_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1532_; 
v_toCommandContextInfo_1505_ = lean_ctor_get(v_ctx_1502_, 0);
lean_inc_ref(v_toCommandContextInfo_1505_);
lean_dec_ref(v_ctx_1502_);
v_fileMap_1506_ = lean_ctor_get(v_toCommandContextInfo_1505_, 2);
lean_inc_ref(v_fileMap_1506_);
lean_dec_ref(v_toCommandContextInfo_1505_);
v___x_1507_ = l_Lean_FileMap_toPosition(v_fileMap_1506_, v_pos_1503_);
v_line_1508_ = lean_ctor_get(v___x_1507_, 0);
v_column_1509_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1511_ = v___x_1507_;
v_isShared_1512_ = v_isSharedCheck_1532_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_column_1509_);
lean_inc(v_line_1508_);
lean_dec(v___x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1532_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1514_ = l_Nat_reprFast(v_line_1508_);
v___x_1515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 5);
lean_ctor_set(v___x_1511_, 1, v___x_1515_);
lean_ctor_set(v___x_1511_, 0, v___x_1513_);
v___x_1517_ = v___x_1511_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_pos_1524_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Nat_reprFast(v_column_1509_);
v___x_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_1524_, 0, v___x_1522_);
lean_ctor_set(v_pos_1524_, 1, v___x_1523_);
switch(lean_obj_tag(v_info_1504_))
{
case 0:
{
return v_pos_1524_;
}
case 1:
{
uint8_t v_canonical_1528_; 
v_canonical_1528_ = lean_ctor_get_uint8(v_info_1504_, sizeof(void*)*2);
if (v_canonical_1528_ == 1)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_pos_1524_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
else
{
goto v___jp_1525_;
}
}
default: 
{
goto v___jp_1525_;
}
}
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_pos_1524_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_1533_, lean_object* v_pos_1534_, lean_object* v_info_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1533_, v_pos_1534_, v_info_1535_);
lean_dec(v_info_1535_);
lean_dec(v_pos_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_1540_, lean_object* v_stx_1541_){
_start:
{
lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___x_1552_; lean_object* v___y_1554_; lean_object* v___x_1557_; 
v___x_1552_ = 0;
v___x_1557_ = l_Lean_Syntax_getPos_x3f(v_stx_1541_, v___x_1552_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_unsigned_to_nat(0u);
v___y_1554_ = v___x_1558_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1559_; 
v_val_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1559_);
lean_dec_ref_known(v___x_1557_, 1);
v___y_1554_ = v_val_1559_;
goto v___jp_1553_;
}
v___jp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1545_ = l_Lean_Syntax_getHeadInfo(v_stx_1541_);
lean_inc_ref(v_ctx_1540_);
v___x_1546_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1540_, v___y_1543_, v___x_1545_);
lean_dec(v___x_1545_);
lean_dec(v___y_1543_);
v___x_1547_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_Syntax_getTailInfo(v_stx_1541_);
v___x_1550_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1540_, v___y_1544_, v___x_1549_);
lean_dec(v___x_1549_);
lean_dec(v___y_1544_);
v___x_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
return v___x_1551_;
}
v___jp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1541_, v___x_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v___y_1554_);
v___y_1543_ = v___y_1554_;
v___y_1544_ = v___y_1554_;
goto v___jp_1542_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___y_1543_ = v___y_1554_;
v___y_1544_ = v_val_1556_;
goto v___jp_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_1560_, lean_object* v_stx_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1560_, v_stx_1561_);
lean_dec(v_stx_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_1566_, lean_object* v_info_1567_){
_start:
{
lean_object* v_elaborator_1568_; lean_object* v_stx_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1584_; 
v_elaborator_1568_ = lean_ctor_get(v_info_1567_, 0);
v_stx_1569_ = lean_ctor_get(v_info_1567_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_info_1567_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1571_ = v_info_1567_;
v_isShared_1572_ = v_isSharedCheck_1584_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_stx_1569_);
lean_inc(v_elaborator_1568_);
lean_dec(v_info_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1584_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___x_1573_; 
v___x_1573_ = l_Lean_Name_isAnonymous(v_elaborator_1568_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1566_, v_stx_1569_);
lean_dec(v_stx_1569_);
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 5);
lean_ctor_set(v___x_1571_, 1, v___x_1575_);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1577_ = v___x_1571_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = 1;
v___x_1579_ = l_Lean_Name_toString(v_elaborator_1568_, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1577_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
return v___x_1581_;
}
}
else
{
lean_object* v___x_1583_; 
lean_del_object(v___x_1571_);
lean_dec(v_elaborator_1568_);
v___x_1583_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1566_, v_stx_1569_);
lean_dec(v_stx_1569_);
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_1585_, lean_object* v_ctx_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v_lctx_1589_; lean_object* v___x_1590_; 
v_lctx_1589_ = lean_ctor_get(v_info_1585_, 1);
lean_inc_ref(v_lctx_1589_);
lean_dec_ref(v_info_1585_);
v___x_1590_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1586_, v_lctx_1589_, v_x_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_1591_, lean_object* v_ctx_1592_, lean_object* v_x_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1591_, v_ctx_1592_, v_x_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_1596_, lean_object* v_info_1597_, lean_object* v_ctx_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1597_, v_ctx_1598_, v_x_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_1602_, lean_object* v_info_1603_, lean_object* v_ctx_1604_, lean_object* v_x_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_1602_, v_info_1603_, v_ctx_1604_, v_x_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_1622_, lean_object* v_toElabInfo_1623_, lean_object* v_expr_1624_, uint8_t v_isBinder_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v_a_1646_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1660_; lean_object* v_a_1661_; lean_object* v___x_1664_; 
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc_ref(v_expr_1624_);
v___x_1664_ = lean_infer_type(v_expr_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = l_Lean_Meta_ppExpr(v_a_1665_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_a_1646_ = v_a_1667_;
goto v___jp_1645_;
}
else
{
lean_object* v_a_1668_; 
v_a_1668_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1668_);
v___y_1660_ = v___x_1666_;
v_a_1661_ = v_a_1668_;
goto v___jp_1659_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1664_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1664_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
lean_inc(v_a_1669_);
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
v___y_1660_ = v___x_1674_;
v_a_1661_ = v_a_1669_;
goto v___jp_1659_;
}
}
}
v___jp_1631_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_inc_ref(v___y_1634_);
v___x_1635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1634_);
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___y_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___y_1633_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1622_, v_toElabInfo_1623_);
v___x_1643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
v___jp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_ppExpr(v_expr_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_1650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_a_1648_);
v___x_1651_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
if (v_isBinder_1625_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_1632_ = v___x_1652_;
v___y_1633_ = v_a_1646_;
v___y_1634_ = v___x_1653_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_1632_ = v___x_1652_;
v___y_1633_ = v_a_1646_;
v___y_1634_ = v___x_1654_;
goto v___jp_1631_;
}
}
else
{
lean_dec(v_a_1646_);
lean_dec_ref(v_toElabInfo_1623_);
lean_dec_ref(v_ctx_1622_);
return v___x_1647_;
}
}
v___jp_1655_:
{
if (v___y_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___y_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_1646_ = v___x_1658_;
goto v___jp_1645_;
}
else
{
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v_expr_1624_);
lean_dec_ref(v_toElabInfo_1623_);
lean_dec_ref(v_ctx_1622_);
return v___y_1656_;
}
}
v___jp_1659_:
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_Exception_isInterrupt(v_a_1661_);
if (v___x_1662_ == 0)
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_Exception_isRuntime(v_a_1661_);
v___y_1656_ = v___y_1660_;
v___y_1657_ = v___x_1663_;
goto v___jp_1655_;
}
else
{
lean_dec_ref(v_a_1661_);
v___y_1656_ = v___y_1660_;
v___y_1657_ = v___x_1662_;
goto v___jp_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_1677_, lean_object* v_toElabInfo_1678_, lean_object* v_expr_1679_, lean_object* v_isBinder_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_isBinder_boxed_1686_; lean_object* v_res_1687_; 
v_isBinder_boxed_1686_ = lean_unbox(v_isBinder_1680_);
v_res_1687_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_1677_, v_toElabInfo_1678_, v_expr_1679_, v_isBinder_boxed_1686_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_1688_, lean_object* v_info_1689_){
_start:
{
lean_object* v_toElabInfo_1691_; lean_object* v_expr_1692_; uint8_t v_isBinder_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; 
v_toElabInfo_1691_ = lean_ctor_get(v_info_1689_, 0);
v_expr_1692_ = lean_ctor_get(v_info_1689_, 3);
v_isBinder_1693_ = lean_ctor_get_uint8(v_info_1689_, sizeof(void*)*4);
v___x_1694_ = lean_box(v_isBinder_1693_);
lean_inc_ref(v_expr_1692_);
lean_inc_ref(v_toElabInfo_1691_);
lean_inc_ref(v_ctx_1688_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1695_, 0, v_ctx_1688_);
lean_closure_set(v___f_1695_, 1, v_toElabInfo_1691_);
lean_closure_set(v___f_1695_, 2, v_expr_1692_);
lean_closure_set(v___f_1695_, 3, v___x_1694_);
v___x_1696_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1689_, v_ctx_1688_, v___f_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_1697_, lean_object* v_info_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_TermInfo_format(v_ctx_1697_, v_info_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_1704_, lean_object* v_info_1705_){
_start:
{
lean_object* v_toElabInfo_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toElabInfo_1706_ = lean_ctor_get(v_info_1705_, 0);
lean_inc_ref(v_toElabInfo_1706_);
lean_dec_ref(v_info_1705_);
v___x_1707_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_1708_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1704_, v_toElabInfo_1706_);
v___x_1709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1717_;
}
else
{
lean_object* v_val_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1728_; 
v_val_1718_ = lean_ctor_get(v_x_1716_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x_1716_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1720_ = v_x_1716_;
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_val_1718_);
lean_dec(v_x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1722_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1723_ = lean_expr_dbg_to_string(v_val_1718_);
lean_dec(v_val_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 3);
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1722_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_1735_, lean_object* v_lctx_1736_, lean_object* v_stx_1737_, lean_object* v_expectedType_x3f_1738_, lean_object* v_info_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1764_; 
v___x_1745_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1735_, v_lctx_1736_, v_stx_1737_);
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1750_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_1751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_a_1746_);
v___x_1752_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1738_);
v___x_1755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_Elab_CompletionInfo_stx(v_info_1739_);
v___x_1759_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1735_, v___x_1758_);
lean_dec(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1760_);
v___x_1762_ = v___x_1748_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_1765_, lean_object* v_lctx_1766_, lean_object* v_stx_1767_, lean_object* v_expectedType_x3f_1768_, lean_object* v_info_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_1765_, v_lctx_1766_, v_stx_1767_, v_expectedType_x3f_1768_, v_info_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v_info_1769_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_1782_, lean_object* v_info_1783_){
_start:
{
switch(lean_obj_tag(v_info_1783_))
{
case 0:
{
lean_object* v_termInfo_1785_; lean_object* v_expectedType_x3f_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1807_; 
v_termInfo_1785_ = lean_ctor_get(v_info_1783_, 0);
v_expectedType_x3f_1786_ = lean_ctor_get(v_info_1783_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_info_1783_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1788_ = v_info_1783_;
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_expectedType_x3f_1786_);
lean_inc(v_termInfo_1785_);
lean_dec(v_info_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Elab_TermInfo_format(v_ctx_1782_, v_termInfo_1785_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1806_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 5);
lean_ctor_set(v___x_1788_, 1, v_a_1791_);
lean_ctor_set(v___x_1788_, 0, v___x_1795_);
v___x_1797_ = v___x_1788_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_a_1791_);
v___x_1797_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1798_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1786_);
v___x_1801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1801_);
v___x_1803_ = v___x_1793_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_del_object(v___x_1788_);
lean_dec(v_expectedType_x3f_1786_);
return v___x_1790_;
}
}
}
case 1:
{
lean_object* v_stx_1808_; lean_object* v_lctx_1809_; lean_object* v_expectedType_x3f_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; 
v_stx_1808_ = lean_ctor_get(v_info_1783_, 0);
lean_inc(v_stx_1808_);
v_lctx_1809_ = lean_ctor_get(v_info_1783_, 2);
lean_inc_ref_n(v_lctx_1809_, 2);
v_expectedType_x3f_1810_ = lean_ctor_get(v_info_1783_, 3);
lean_inc(v_expectedType_x3f_1810_);
lean_inc_ref(v_ctx_1782_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1811_, 0, v_ctx_1782_);
lean_closure_set(v___f_1811_, 1, v_lctx_1809_);
lean_closure_set(v___f_1811_, 2, v_stx_1808_);
lean_closure_set(v___f_1811_, 3, v_expectedType_x3f_1810_);
lean_closure_set(v___f_1811_, 4, v_info_1783_);
v___x_1812_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1782_, v_lctx_1809_, v___f_1811_);
return v___x_1812_;
}
default: 
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1813_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_1814_ = l_Lean_Elab_CompletionInfo_stx(v_info_1783_);
lean_dec_ref(v_info_1783_);
v___x_1815_ = lean_box(0);
v___x_1816_ = 0;
lean_inc(v___x_1814_);
v___x_1817_ = l_Lean_Syntax_formatStx(v___x_1814_, v___x_1815_, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1782_, v___x_1814_);
lean_dec(v___x_1814_);
v___x_1822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_1824_, lean_object* v_info_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1824_, v_info_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_1831_, lean_object* v_info_1832_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_1835_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1831_, v_info_1832_);
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_1838_, lean_object* v_info_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Elab_CommandInfo_format(v_ctx_1838_, v_info_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_1845_, lean_object* v_info_1846_){
_start:
{
lean_object* v_stx_1848_; lean_object* v_optionName_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_stx_1848_ = lean_ctor_get(v_info_1846_, 0);
lean_inc(v_stx_1848_);
v_optionName_1849_ = lean_ctor_get(v_info_1846_, 1);
lean_inc(v_optionName_1849_);
lean_dec_ref(v_info_1846_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_1851_ = 1;
v___x_1852_ = l_Lean_Name_toString(v_optionName_1849_, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1845_, v_stx_1848_);
lean_dec(v_stx_1848_);
v___x_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_1860_, lean_object* v_info_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Elab_OptionInfo_format(v_ctx_1860_, v_info_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_1867_, lean_object* v_info_1868_){
_start:
{
lean_object* v_stx_1870_; lean_object* v_errorName_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1887_; 
v_stx_1870_ = lean_ctor_get(v_info_1868_, 0);
v_errorName_1871_ = lean_ctor_get(v_info_1868_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_info_1868_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1873_ = v_info_1868_;
v_isShared_1874_ = v_isSharedCheck_1887_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_errorName_1871_);
lean_inc(v_stx_1870_);
lean_dec(v_info_1868_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1887_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1875_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_1876_ = 1;
v___x_1877_ = l_Lean_Name_toString(v_errorName_1871_, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 5);
lean_ctor_set(v___x_1873_, 1, v___x_1878_);
lean_ctor_set(v___x_1873_, 0, v___x_1875_);
v___x_1880_ = v___x_1873_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1867_, v_stx_1870_);
lean_dec(v_stx_1870_);
v___x_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_1888_, lean_object* v_info_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1888_, v_info_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1898_, lean_object* v_fieldName_1899_, lean_object* v_ctx_1900_, lean_object* v_stx_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc_ref(v_val_1898_);
v___x_1907_ = lean_infer_type(v_val_1898_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_Meta_ppExpr(v_a_1908_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1940_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1940_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1940_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Meta_ppExpr(v_val_1898_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1939_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1939_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1939_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1919_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1920_ = 1;
v___x_1921_ = l_Lean_Name_toString(v_fieldName_1899_, v___x_1920_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 3);
lean_ctor_set(v___x_1912_, 0, v___x_1921_);
v___x_1923_ = v___x_1912_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1919_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v_a_1910_);
v___x_1928_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_a_1915_);
v___x_1931_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1900_, v_stx_1901_);
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1934_);
v___x_1936_ = v___x_1917_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_del_object(v___x_1912_);
lean_dec(v_a_1910_);
lean_dec_ref(v_ctx_1900_);
lean_dec(v_fieldName_1899_);
return v___x_1914_;
}
}
}
else
{
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec_ref(v_ctx_1900_);
lean_dec(v_fieldName_1899_);
lean_dec_ref(v_val_1898_);
return v___x_1909_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec_ref(v_ctx_1900_);
lean_dec(v_fieldName_1899_);
lean_dec_ref(v_val_1898_);
v_a_1941_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1907_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1907_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1949_, lean_object* v_fieldName_1950_, lean_object* v_ctx_1951_, lean_object* v_stx_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1949_, v_fieldName_1950_, v_ctx_1951_, v_stx_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v_stx_1952_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1959_, lean_object* v_info_1960_){
_start:
{
lean_object* v_fieldName_1962_; lean_object* v_lctx_1963_; lean_object* v_val_1964_; lean_object* v_stx_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v_fieldName_1962_ = lean_ctor_get(v_info_1960_, 1);
lean_inc(v_fieldName_1962_);
v_lctx_1963_ = lean_ctor_get(v_info_1960_, 2);
lean_inc_ref(v_lctx_1963_);
v_val_1964_ = lean_ctor_get(v_info_1960_, 3);
lean_inc_ref(v_val_1964_);
v_stx_1965_ = lean_ctor_get(v_info_1960_, 4);
lean_inc(v_stx_1965_);
lean_dec_ref(v_info_1960_);
lean_inc_ref(v_ctx_1959_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1966_, 0, v_val_1964_);
lean_closure_set(v___f_1966_, 1, v_fieldName_1962_);
lean_closure_set(v___f_1966_, 2, v_ctx_1959_);
lean_closure_set(v___f_1966_, 3, v_stx_1965_);
v___x_1967_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1959_, v_lctx_1963_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1968_, lean_object* v_info_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Elab_FieldInfo_format(v_ctx_1968_, v_info_1969_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 0)
{
lean_dec(v_pre_1972_);
return v_x_1973_;
}
else
{
lean_object* v_head_1975_; lean_object* v_tail_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1985_; 
v_head_1975_ = lean_ctor_get(v_x_1974_, 0);
v_tail_1976_ = lean_ctor_get(v_x_1974_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_x_1974_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1978_ = v_x_1974_;
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_tail_1976_);
lean_inc(v_head_1975_);
lean_dec(v_x_1974_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
lean_inc(v_pre_1972_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 5);
lean_ctor_set(v___x_1978_, 1, v_pre_1972_);
lean_ctor_set(v___x_1978_, 0, v_x_1973_);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_x_1973_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_pre_1972_);
v___x_1981_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_head_1975_);
v_x_1973_ = v___x_1982_;
v_x_1974_ = v_tail_1976_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1986_, lean_object* v_x_1987_){
_start:
{
if (lean_obj_tag(v_x_1987_) == 0)
{
lean_object* v___x_1988_; 
lean_dec(v_pre_1986_);
v___x_1988_ = lean_box(0);
return v___x_1988_;
}
else
{
lean_object* v_head_1989_; lean_object* v_tail_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_head_1989_ = lean_ctor_get(v_x_1987_, 0);
v_tail_1990_ = lean_ctor_get(v_x_1987_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v_x_1987_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_tail_1990_);
lean_inc(v_head_1989_);
lean_dec(v_x_1987_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
lean_inc(v_pre_1986_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 5);
lean_ctor_set(v___x_1992_, 1, v_head_1989_);
lean_ctor_set(v___x_1992_, 0, v_pre_1986_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_pre_1986_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_head_1989_);
v___x_1995_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1986_, v___x_1995_, v_tail_1990_);
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = l_List_reverse___redArg(v_x_2000_);
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
return v___x_2007_;
}
else
{
lean_object* v_head_2008_; lean_object* v_tail_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2027_; 
v_head_2008_ = lean_ctor_get(v_x_1999_, 0);
v_tail_2009_ = lean_ctor_get(v_x_1999_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_x_1999_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2011_ = v_x_1999_;
v_isShared_2012_ = v_isSharedCheck_2027_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_tail_2009_);
lean_inc(v_head_2008_);
lean_dec(v_x_1999_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2027_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Meta_ppGoal(v_head_2008_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v_head_2008_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v_x_2000_);
lean_ctor_set(v___x_2011_, 0, v_a_2014_);
v___x_2016_ = v___x_2011_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_x_2000_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v_x_1999_ = v_tail_2009_;
v_x_2000_ = v___x_2016_;
goto _start;
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_2011_);
lean_dec(v_tail_2009_);
lean_dec(v_x_2000_);
v_a_2019_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2013_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2013_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_2039_, lean_object* v___x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_2039_, v___x_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2056_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2051_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2052_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2051_, v_a_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2046_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2046_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_2065_, lean_object* v___x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_2065_, v___x_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_unsigned_to_nat(32u);
v___x_2077_ = lean_mk_empty_array_with_capacity(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2079_ = ((size_t)5ULL);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_unsigned_to_nat(32u);
v___x_2082_ = lean_mk_empty_array_with_capacity(v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2084_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2080_);
lean_ctor_set(v___x_2084_, 3, v___x_2080_);
lean_ctor_set_usize(v___x_2084_, 4, v___x_2079_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(1);
v___x_2086_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2087_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_2088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___x_2085_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_2092_, lean_object* v_goals_2093_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_List_isEmpty___redArg(v_goals_2093_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; 
v___x_2096_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_2097_ = lean_box(0);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2098_, 0, v_goals_2093_);
lean_closure_set(v___f_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_2092_, v___x_2096_, v___f_2098_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v_goals_2093_);
lean_dec_ref(v_ctx_2092_);
v___x_2100_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_2102_, lean_object* v_goals_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_2102_, v_goals_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_2115_, lean_object* v_info_2116_){
_start:
{
lean_object* v_toCommandContextInfo_2118_; lean_object* v_parentDecl_x3f_2119_; lean_object* v_autoImplicits_2120_; lean_object* v_env_2121_; lean_object* v_cmdEnv_x3f_2122_; lean_object* v_fileMap_2123_; lean_object* v_options_2124_; lean_object* v_currNamespace_2125_; lean_object* v_openDecls_2126_; lean_object* v_ngen_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2169_; 
v_toCommandContextInfo_2118_ = lean_ctor_get(v_ctx_2115_, 0);
lean_inc_ref(v_toCommandContextInfo_2118_);
v_parentDecl_x3f_2119_ = lean_ctor_get(v_ctx_2115_, 1);
v_autoImplicits_2120_ = lean_ctor_get(v_ctx_2115_, 2);
v_env_2121_ = lean_ctor_get(v_toCommandContextInfo_2118_, 0);
v_cmdEnv_x3f_2122_ = lean_ctor_get(v_toCommandContextInfo_2118_, 1);
v_fileMap_2123_ = lean_ctor_get(v_toCommandContextInfo_2118_, 2);
v_options_2124_ = lean_ctor_get(v_toCommandContextInfo_2118_, 4);
v_currNamespace_2125_ = lean_ctor_get(v_toCommandContextInfo_2118_, 5);
v_openDecls_2126_ = lean_ctor_get(v_toCommandContextInfo_2118_, 6);
v_ngen_2127_ = lean_ctor_get(v_toCommandContextInfo_2118_, 7);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_toCommandContextInfo_2118_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_toCommandContextInfo_2118_, 3);
lean_dec(v_unused_2170_);
v___x_2129_ = v_toCommandContextInfo_2118_;
v_isShared_2130_ = v_isSharedCheck_2169_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_ngen_2127_);
lean_inc(v_openDecls_2126_);
lean_inc(v_currNamespace_2125_);
lean_inc(v_options_2124_);
lean_inc(v_fileMap_2123_);
lean_inc(v_cmdEnv_x3f_2122_);
lean_inc(v_env_2121_);
lean_dec(v_toCommandContextInfo_2118_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2169_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_toElabInfo_2131_; lean_object* v_mctxBefore_2132_; lean_object* v_goalsBefore_2133_; lean_object* v_mctxAfter_2134_; lean_object* v_goalsAfter_2135_; lean_object* v___x_2137_; 
v_toElabInfo_2131_ = lean_ctor_get(v_info_2116_, 0);
lean_inc_ref(v_toElabInfo_2131_);
v_mctxBefore_2132_ = lean_ctor_get(v_info_2116_, 1);
lean_inc_ref(v_mctxBefore_2132_);
v_goalsBefore_2133_ = lean_ctor_get(v_info_2116_, 2);
lean_inc(v_goalsBefore_2133_);
v_mctxAfter_2134_ = lean_ctor_get(v_info_2116_, 3);
lean_inc_ref(v_mctxAfter_2134_);
v_goalsAfter_2135_ = lean_ctor_get(v_info_2116_, 4);
lean_inc(v_goalsAfter_2135_);
lean_dec_ref(v_info_2116_);
lean_inc_ref(v_ngen_2127_);
lean_inc(v_openDecls_2126_);
lean_inc(v_currNamespace_2125_);
lean_inc_ref(v_options_2124_);
lean_inc_ref(v_fileMap_2123_);
lean_inc(v_cmdEnv_x3f_2122_);
lean_inc_ref(v_env_2121_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 3, v_mctxBefore_2132_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_env_2121_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_cmdEnv_x3f_2122_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_fileMap_2123_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_mctxBefore_2132_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_options_2124_);
lean_ctor_set(v_reuseFailAlloc_2168_, 5, v_currNamespace_2125_);
lean_ctor_set(v_reuseFailAlloc_2168_, 6, v_openDecls_2126_);
lean_ctor_set(v_reuseFailAlloc_2168_, 7, v_ngen_2127_);
v___x_2137_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v_ctxB_2138_; lean_object* v___x_2139_; 
lean_inc_ref(v_autoImplicits_2120_);
lean_inc(v_parentDecl_x3f_2119_);
v_ctxB_2138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_2138_, 0, v___x_2137_);
lean_ctor_set(v_ctxB_2138_, 1, v_parentDecl_x3f_2119_);
lean_ctor_set(v_ctxB_2138_, 2, v_autoImplicits_2120_);
v___x_2139_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_2138_, v_goalsBefore_2133_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v_ctxA_2142_; lean_object* v___x_2143_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2141_, 0, v_env_2121_);
lean_ctor_set(v___x_2141_, 1, v_cmdEnv_x3f_2122_);
lean_ctor_set(v___x_2141_, 2, v_fileMap_2123_);
lean_ctor_set(v___x_2141_, 3, v_mctxAfter_2134_);
lean_ctor_set(v___x_2141_, 4, v_options_2124_);
lean_ctor_set(v___x_2141_, 5, v_currNamespace_2125_);
lean_ctor_set(v___x_2141_, 6, v_openDecls_2126_);
lean_ctor_set(v___x_2141_, 7, v_ngen_2127_);
lean_inc_ref(v_autoImplicits_2120_);
lean_inc(v_parentDecl_x3f_2119_);
v_ctxA_2142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_2142_, 0, v___x_2141_);
lean_ctor_set(v_ctxA_2142_, 1, v_parentDecl_x3f_2119_);
lean_ctor_set(v_ctxA_2142_, 2, v_autoImplicits_2120_);
v___x_2143_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_2142_, v_goalsAfter_2135_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2167_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2167_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2167_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_stx_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v_stx_2148_ = lean_ctor_get(v_toElabInfo_2131_, 1);
lean_inc(v_stx_2148_);
v___x_2149_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_2150_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2115_, v_toElabInfo_2131_);
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_box(0);
v___x_2155_ = 0;
v___x_2156_ = l_Lean_Syntax_formatStx(v_stx_2148_, v___x_2154_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2153_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v_a_2140_);
v___x_2161_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_2162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v_a_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2163_);
v___x_2165_ = v___x_2146_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_dec(v_a_2140_);
lean_dec_ref(v_toElabInfo_2131_);
lean_dec_ref(v_ctx_2115_);
return v___x_2143_;
}
}
else
{
lean_dec(v_goalsAfter_2135_);
lean_dec_ref(v_mctxAfter_2134_);
lean_dec_ref(v_toElabInfo_2131_);
lean_dec_ref(v_ngen_2127_);
lean_dec(v_openDecls_2126_);
lean_dec(v_currNamespace_2125_);
lean_dec_ref(v_options_2124_);
lean_dec_ref(v_fileMap_2123_);
lean_dec(v_cmdEnv_x3f_2122_);
lean_dec_ref(v_env_2121_);
lean_dec_ref(v_ctx_2115_);
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_2171_, lean_object* v_info_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Elab_TacticInfo_format(v_ctx_2171_, v_info_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_2181_, lean_object* v_info_2182_){
_start:
{
lean_object* v_lctx_2184_; lean_object* v_stx_2185_; lean_object* v_output_2186_; lean_object* v___x_2187_; lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2202_; 
v_lctx_2184_ = lean_ctor_get(v_info_2182_, 0);
lean_inc_ref_n(v_lctx_2184_, 2);
v_stx_2185_ = lean_ctor_get(v_info_2182_, 1);
lean_inc(v_stx_2185_);
v_output_2186_ = lean_ctor_get(v_info_2182_, 2);
lean_inc(v_output_2186_);
lean_dec_ref(v_info_2182_);
v___x_2187_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2181_, v_lctx_2184_, v_stx_2185_);
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2181_, v_lctx_2184_, v_output_2186_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2194_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_2195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_a_2188_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_2197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v_a_2190_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2198_);
v___x_2200_ = v___x_2192_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_2203_, lean_object* v_info_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2203_, v_info_2204_);
lean_dec_ref(v_ctx_2203_);
return v_res_2206_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = 1;
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_2213_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
lean_ctor_set_usize(v___x_2213_, 2, v___x_2211_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*3, v___x_2210_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_2217_){
_start:
{
lean_object* v_toWidgetInstance_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2247_; 
v_toWidgetInstance_2218_ = lean_ctor_get(v_info_2217_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_info_2217_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v_info_2217_, 1);
lean_dec(v_unused_2248_);
v___x_2220_ = v_info_2217_;
v_isShared_2221_ = v_isSharedCheck_2247_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_toWidgetInstance_2218_);
lean_dec(v_info_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2247_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_id_2222_; lean_object* v_props_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_fst_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2245_; 
v_id_2222_ = lean_ctor_get(v_toWidgetInstance_2218_, 0);
lean_inc(v_id_2222_);
v_props_2223_ = lean_ctor_get(v_toWidgetInstance_2218_, 1);
lean_inc_ref(v_props_2223_);
lean_dec_ref(v_toWidgetInstance_2218_);
v___x_2224_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_2225_ = lean_apply_1(v_props_2223_, v___x_2224_);
v_fst_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2225_, 1);
lean_dec(v_unused_2246_);
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_fst_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2230_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_2231_ = 1;
v___x_2232_ = l_Lean_Name_toString(v_id_2222_, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set_tag(v___x_2228_, 5);
lean_ctor_set(v___x_2228_, 1, v___x_2233_);
lean_ctor_set(v___x_2228_, 0, v___x_2230_);
v___x_2235_ = v___x_2228_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_2221_ == 0)
{
lean_ctor_set_tag(v___x_2220_, 5);
lean_ctor_set(v___x_2220_, 1, v___x_2236_);
lean_ctor_set(v___x_2220_, 0, v___x_2235_);
v___x_2238_ = v___x_2220_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = lean_unsigned_to_nat(80u);
v___x_2240_ = l_Lean_Json_pretty(v_fst_2226_, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2238_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
return v___x_2242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_2255_){
_start:
{
lean_object* v_userName_2256_; lean_object* v_id_2257_; lean_object* v_baseId_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_userName_2256_ = lean_ctor_get(v_info_2255_, 0);
lean_inc(v_userName_2256_);
v_id_2257_ = lean_ctor_get(v_info_2255_, 1);
lean_inc(v_id_2257_);
v_baseId_2258_ = lean_ctor_get(v_info_2255_, 2);
lean_inc(v_baseId_2258_);
lean_dec_ref(v_info_2255_);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_2260_ = lean_erase_macro_scopes(v_userName_2256_);
v___x_2261_ = 1;
v___x_2262_ = l_Lean_Name_toString(v___x_2260_, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2259_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_2266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_Name_toString(v_id_2257_, v___x_2261_);
v___x_2268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2266_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_Name_toString(v_baseId_2258_, v___x_2261_);
v___x_2273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2271_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_2278_, lean_object* v_info_2279_){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_2281_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_2278_, v_info_2279_);
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_2283_, lean_object* v_info_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2283_, v_info_2284_);
lean_dec(v_info_2284_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_2288_, lean_object* v_info_2289_){
_start:
{
lean_object* v_mkDocString_x3f_2291_; 
v_mkDocString_x3f_2291_ = lean_ctor_get(v_info_2289_, 2);
lean_inc(v_mkDocString_x3f_2291_);
lean_dec_ref(v_info_2289_);
if (lean_obj_tag(v_mkDocString_x3f_2291_) == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_ppCtx_2288_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
else
{
lean_object* v_val_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2326_; 
v_val_2294_ = lean_ctor_get(v_mkDocString_x3f_2291_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_mkDocString_x3f_2291_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2296_ = v_mkDocString_x3f_2291_;
v_isShared_2297_ = v_isSharedCheck_2326_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_val_2294_);
lean_dec(v_mkDocString_x3f_2291_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2326_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_apply_2(v_val_2294_, v_ppCtx_2288_, lean_box(0));
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2309_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_a_2299_);
v___x_2304_ = v___x_2296_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2325_; 
v_a_2310_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2312_ = v___x_2298_;
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2298_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2314_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_2315_ = lean_io_error_to_string(v_a_2310_);
v___x_2316_ = lean_string_append(v___x_2314_, v___x_2315_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2318_ = lean_string_append(v___x_2316_, v___x_2317_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2318_);
v___x_2320_ = v___x_2296_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2320_);
v___x_2322_ = v___x_2312_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_2327_, lean_object* v_info_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_2327_, v_info_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2333_;
}
else
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2345_; 
v_val_2334_ = lean_ctor_get(v_x_2331_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2331_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2336_ = v_x_2331_;
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_x_2331_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2338_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2339_ = l_String_quote(v_val_2334_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 3);
lean_ctor_set(v___x_2336_, 0, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2338_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Repr_addAppParen(v___x_2342_, v_x_2332_);
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2346_, v_x_2347_);
lean_dec(v_x_2347_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2363_, lean_object* v_info_2364_){
_start:
{
lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v_toTermInfo_2372_; lean_object* v_location_x3f_2373_; uint8_t v_explicit_2374_; lean_object* v___y_2376_; 
v_toTermInfo_2372_ = lean_ctor_get(v_info_2364_, 0);
lean_inc_ref(v_toTermInfo_2372_);
v_location_x3f_2373_ = lean_ctor_get(v_info_2364_, 1);
lean_inc(v_location_x3f_2373_);
v_explicit_2374_ = lean_ctor_get_uint8(v_info_2364_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_2373_) == 1)
{
lean_object* v_val_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2458_; 
v_val_2397_ = lean_ctor_get(v_location_x3f_2373_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_location_x3f_2373_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2399_ = v_location_x3f_2373_;
v_isShared_2400_ = v_isSharedCheck_2458_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_val_2397_);
lean_dec(v_location_x3f_2373_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2458_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_range_2401_; lean_object* v_pos_2402_; lean_object* v_endPos_2403_; lean_object* v_module_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2456_; 
v_range_2401_ = lean_ctor_get(v_val_2397_, 1);
v_pos_2402_ = lean_ctor_get(v_range_2401_, 0);
lean_inc_ref(v_pos_2402_);
v_endPos_2403_ = lean_ctor_get(v_range_2401_, 2);
lean_inc_ref(v_endPos_2403_);
v_module_2404_ = lean_ctor_get(v_val_2397_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_val_2397_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v_val_2397_, 1);
lean_dec(v_unused_2457_);
v___x_2406_ = v_val_2397_;
v_isShared_2407_ = v_isSharedCheck_2456_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_module_2404_);
lean_dec(v_val_2397_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2456_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_line_2408_; lean_object* v_column_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2455_; 
v_line_2408_ = lean_ctor_get(v_pos_2402_, 0);
v_column_2409_ = lean_ctor_get(v_pos_2402_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_pos_2402_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2411_ = v_pos_2402_;
v_isShared_2412_ = v_isSharedCheck_2455_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_column_2409_);
lean_inc(v_line_2408_);
lean_dec(v_pos_2402_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2455_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_line_2413_; lean_object* v_column_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2454_; 
v_line_2413_ = lean_ctor_get(v_endPos_2403_, 0);
v_column_2414_ = lean_ctor_get(v_endPos_2403_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_endPos_2403_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2416_ = v_endPos_2403_;
v_isShared_2417_ = v_isSharedCheck_2454_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_column_2414_);
lean_inc(v_line_2413_);
lean_dec(v_endPos_2403_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2454_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = 1;
v___x_2419_ = l_Lean_Name_toString(v_module_2404_, v___x_2418_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set_tag(v___x_2399_, 3);
lean_ctor_set(v___x_2399_, 0, v___x_2419_);
v___x_2421_ = v___x_2399_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 5);
lean_ctor_set(v___x_2416_, 1, v___x_2422_);
lean_ctor_set(v___x_2416_, 0, v___x_2421_);
v___x_2424_ = v___x_2416_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2426_ = l_Nat_reprFast(v_line_2408_);
v___x_2427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 5);
lean_ctor_set(v___x_2411_, 1, v___x_2427_);
lean_ctor_set(v___x_2411_, 0, v___x_2425_);
v___x_2429_ = v___x_2411_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 5);
lean_ctor_set(v___x_2406_, 1, v___x_2430_);
lean_ctor_set(v___x_2406_, 0, v___x_2429_);
v___x_2432_ = v___x_2406_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2433_ = l_Nat_reprFast(v_column_2409_);
v___x_2434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2432_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2424_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Nat_reprFast(v_line_2413_);
v___x_2442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2425_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___x_2430_);
v___x_2445_ = l_Nat_reprFast(v_column_2414_);
v___x_2446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2436_);
v___x_2449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2440_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___y_2376_ = v___x_2449_;
goto v___jp_2375_;
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
lean_object* v___x_2459_; 
lean_dec(v_location_x3f_2373_);
v___x_2459_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2376_ = v___x_2459_;
goto v___jp_2375_;
}
v___jp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_inc_ref(v___y_2368_);
v___x_2369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___y_2368_);
v___x_2370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___y_2367_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
v___jp_2375_:
{
lean_object* v_lctx_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_lctx_2377_ = lean_ctor_get(v_toTermInfo_2372_, 1);
lean_inc_ref(v_lctx_2377_);
v___x_2378_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_2363_, v_lctx_2377_);
v___x_2379_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_2378_, v_info_2364_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = l_Lean_Elab_TermInfo_format(v_ctx_2363_, v_toTermInfo_2372_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v_a_2382_);
v___x_2385_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___y_2376_);
v___x_2388_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_2380_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
if (v_explicit_2374_ == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2367_ = v___x_2394_;
v___y_2368_ = v___x_2395_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2367_ = v___x_2394_;
v___y_2368_ = v___x_2396_;
goto v___jp_2366_;
}
}
else
{
lean_dec(v_a_2380_);
lean_dec(v___y_2376_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2460_, lean_object* v_info_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2460_, v_info_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2467_, lean_object* v_info_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2470_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2467_, v_info_2468_);
v___x_2471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2475_, lean_object* v_info_2476_){
_start:
{
lean_object* v_stx_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_stx_2477_ = lean_ctor_get(v_info_2476_, 1);
v___x_2478_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2477_);
v___x_2479_ = l_Lean_Syntax_getKind(v_stx_2477_);
v___x_2480_ = 1;
v___x_2481_ = l_Lean_Name_toString(v___x_2479_, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2478_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2475_, v_info_2476_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2497_, lean_object* v_info_2498_){
_start:
{
lean_object* v_toElabInfo_2499_; lean_object* v_name_2500_; uint8_t v_kind_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_toElabInfo_2499_ = lean_ctor_get(v_info_2498_, 0);
lean_inc_ref(v_toElabInfo_2499_);
v_name_2500_ = lean_ctor_get(v_info_2498_, 1);
lean_inc(v_name_2500_);
v_kind_2501_ = lean_ctor_get_uint8(v_info_2498_, sizeof(void*)*2);
lean_dec_ref(v_info_2498_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2503_ = 1;
v___x_2504_ = l_Lean_Name_toString(v_name_2500_, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2502_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2501_, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2497_, v_toElabInfo_2499_);
v___x_2515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2516_, lean_object* v_x_2517_){
_start:
{
switch(lean_obj_tag(v_x_2517_))
{
case 0:
{
lean_object* v_i_2519_; lean_object* v___x_2520_; 
v_i_2519_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2519_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2520_ = l_Lean_Elab_TacticInfo_format(v_ctx_2516_, v_i_2519_);
return v___x_2520_;
}
case 1:
{
lean_object* v_i_2521_; lean_object* v___x_2522_; 
v_i_2521_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2521_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2522_ = l_Lean_Elab_TermInfo_format(v_ctx_2516_, v_i_2521_);
return v___x_2522_;
}
case 2:
{
lean_object* v_i_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
v_i_2523_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2525_ = v_x_2517_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_i_2523_);
lean_dec(v_x_2517_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2516_, v_i_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set_tag(v___x_2525_, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
case 3:
{
lean_object* v_i_2532_; lean_object* v___x_2533_; 
v_i_2532_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2532_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2533_ = l_Lean_Elab_CommandInfo_format(v_ctx_2516_, v_i_2532_);
return v___x_2533_;
}
case 4:
{
lean_object* v_i_2534_; lean_object* v___x_2535_; 
v_i_2534_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2534_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2535_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2516_, v_i_2534_);
lean_dec_ref(v_ctx_2516_);
return v___x_2535_;
}
case 5:
{
lean_object* v_i_2536_; lean_object* v___x_2537_; 
v_i_2536_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2536_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2537_ = l_Lean_Elab_OptionInfo_format(v_ctx_2516_, v_i_2536_);
return v___x_2537_;
}
case 6:
{
lean_object* v_i_2538_; lean_object* v___x_2539_; 
v_i_2538_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2538_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2539_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2516_, v_i_2538_);
return v___x_2539_;
}
case 7:
{
lean_object* v_i_2540_; lean_object* v___x_2541_; 
v_i_2540_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2540_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2541_ = l_Lean_Elab_FieldInfo_format(v_ctx_2516_, v_i_2540_);
return v___x_2541_;
}
case 8:
{
lean_object* v_i_2542_; lean_object* v___x_2543_; 
v_i_2542_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2542_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2543_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2516_, v_i_2542_);
return v___x_2543_;
}
case 9:
{
lean_object* v_i_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_ctx_2516_);
v_i_2544_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2546_ = v_x_2517_;
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_i_2544_);
lean_dec(v_x_2517_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2544_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2548_);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
case 10:
{
lean_object* v_i_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_ctx_2516_);
v_i_2553_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2555_ = v_x_2517_;
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_i_2553_);
lean_dec(v_x_2517_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = l_Lean_Elab_CustomInfo_format(v_i_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
case 11:
{
lean_object* v_i_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_ctx_2516_);
v_i_2562_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v_x_2517_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_i_2562_);
lean_dec(v_x_2517_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
case 12:
{
lean_object* v_i_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2579_; 
v_i_2571_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2573_ = v_x_2517_;
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_i_2571_);
lean_dec(v_x_2517_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2516_, v_i_2571_);
lean_dec(v_i_2571_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
case 13:
{
lean_object* v_i_2580_; lean_object* v___x_2581_; 
v_i_2580_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_i_2580_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2581_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2516_, v_i_2580_);
return v___x_2581_;
}
case 14:
{
lean_object* v_i_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
v_i_2582_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v_x_2517_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_i_2582_);
lean_dec(v_x_2517_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2516_, v_i_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
case 15:
{
lean_object* v_i_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
v_i_2591_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2593_ = v_x_2517_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_i_2591_);
lean_dec(v_x_2517_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = l_Lean_Elab_DocInfo_format(v_ctx_2516_, v_i_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
default: 
{
lean_object* v_i_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
v_i_2600_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2602_ = v_x_2517_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_i_2600_);
lean_dec(v_x_2517_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2516_, v_i_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2609_, lean_object* v_x_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Elab_Info_format(v_ctx_2609_, v_x_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2613_){
_start:
{
switch(lean_obj_tag(v_x_2613_))
{
case 0:
{
lean_object* v_i_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2622_; 
v_i_2614_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2616_ = v_x_2613_;
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_i_2614_);
lean_dec(v_x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_toElabInfo_2618_; lean_object* v___x_2620_; 
v_toElabInfo_2618_ = lean_ctor_get(v_i_2614_, 0);
lean_inc_ref(v_toElabInfo_2618_);
lean_dec_ref(v_i_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 1);
lean_ctor_set(v___x_2616_, 0, v_toElabInfo_2618_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_toElabInfo_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
case 1:
{
lean_object* v_i_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
v_i_2623_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2625_ = v_x_2613_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_i_2623_);
lean_dec(v_x_2613_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_toElabInfo_2627_; lean_object* v___x_2629_; 
v_toElabInfo_2627_ = lean_ctor_get(v_i_2623_, 0);
lean_inc_ref(v_toElabInfo_2627_);
lean_dec_ref(v_i_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_toElabInfo_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_toElabInfo_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
case 2:
{
lean_object* v_i_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2640_; 
v_i_2632_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2634_ = v_x_2613_;
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_i_2632_);
lean_dec(v_x_2613_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_toElabInfo_2636_; lean_object* v___x_2638_; 
v_toElabInfo_2636_ = lean_ctor_get(v_i_2632_, 0);
lean_inc_ref(v_toElabInfo_2636_);
lean_dec_ref(v_i_2632_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
lean_ctor_set(v___x_2634_, 0, v_toElabInfo_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_toElabInfo_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
case 3:
{
lean_object* v_i_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_i_2641_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v_x_2613_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_i_2641_);
lean_dec(v_x_2613_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_i_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
case 13:
{
lean_object* v_i_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2658_; 
v_i_2649_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2651_ = v_x_2613_;
v_isShared_2652_ = v_isSharedCheck_2658_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_i_2649_);
lean_dec(v_x_2613_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2658_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_toTermInfo_2653_; lean_object* v_toElabInfo_2654_; lean_object* v___x_2656_; 
v_toTermInfo_2653_ = lean_ctor_get(v_i_2649_, 0);
lean_inc_ref(v_toTermInfo_2653_);
lean_dec_ref(v_i_2649_);
v_toElabInfo_2654_ = lean_ctor_get(v_toTermInfo_2653_, 0);
lean_inc_ref(v_toElabInfo_2654_);
lean_dec_ref(v_toTermInfo_2653_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
lean_ctor_set(v___x_2651_, 0, v_toElabInfo_2654_);
v___x_2656_ = v___x_2651_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_toElabInfo_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
case 14:
{
lean_object* v_i_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_i_2659_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v_x_2613_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_i_2659_);
lean_dec(v_x_2613_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_i_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
case 15:
{
lean_object* v_i_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_i_2667_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v_x_2613_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_i_2667_);
lean_dec(v_x_2613_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_i_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
case 16:
{
lean_object* v_i_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2683_; 
v_i_2675_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2677_ = v_x_2613_;
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_i_2675_);
lean_dec(v_x_2613_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_toElabInfo_2679_; lean_object* v___x_2681_; 
v_toElabInfo_2679_ = lean_ctor_get(v_i_2675_, 0);
lean_inc_ref(v_toElabInfo_2679_);
lean_dec_ref(v_i_2675_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 1);
lean_ctor_set(v___x_2677_, 0, v_toElabInfo_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_toElabInfo_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
default: 
{
lean_object* v___x_2684_; 
lean_dec_ref(v_x_2613_);
v___x_2684_ = lean_box(0);
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2685_, lean_object* v_x_2686_){
_start:
{
if (lean_obj_tag(v_x_2685_) == 1)
{
if (lean_obj_tag(v_x_2686_) == 0)
{
lean_object* v_val_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2722_; 
v_val_2687_ = lean_ctor_get(v_x_2685_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_x_2685_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2689_ = v_x_2685_;
v_isShared_2690_ = v_isSharedCheck_2722_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_val_2687_);
lean_dec(v_x_2685_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2722_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_toCommandContextInfo_2691_; lean_object* v_i_2692_; lean_object* v_parentDecl_x3f_2693_; lean_object* v_autoImplicits_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2720_; 
v_toCommandContextInfo_2691_ = lean_ctor_get(v_val_2687_, 0);
lean_inc_ref(v_toCommandContextInfo_2691_);
v_i_2692_ = lean_ctor_get(v_x_2686_, 0);
v_parentDecl_x3f_2693_ = lean_ctor_get(v_val_2687_, 1);
v_autoImplicits_2694_ = lean_ctor_get(v_val_2687_, 2);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_val_2687_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; 
v_unused_2721_ = lean_ctor_get(v_val_2687_, 0);
lean_dec(v_unused_2721_);
v___x_2696_ = v_val_2687_;
v_isShared_2697_ = v_isSharedCheck_2720_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_autoImplicits_2694_);
lean_inc(v_parentDecl_x3f_2693_);
lean_dec(v_val_2687_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2720_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_env_2698_; lean_object* v_cmdEnv_x3f_2699_; lean_object* v_fileMap_2700_; lean_object* v_options_2701_; lean_object* v_currNamespace_2702_; lean_object* v_openDecls_2703_; lean_object* v_ngen_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2718_; 
v_env_2698_ = lean_ctor_get(v_toCommandContextInfo_2691_, 0);
v_cmdEnv_x3f_2699_ = lean_ctor_get(v_toCommandContextInfo_2691_, 1);
v_fileMap_2700_ = lean_ctor_get(v_toCommandContextInfo_2691_, 2);
v_options_2701_ = lean_ctor_get(v_toCommandContextInfo_2691_, 4);
v_currNamespace_2702_ = lean_ctor_get(v_toCommandContextInfo_2691_, 5);
v_openDecls_2703_ = lean_ctor_get(v_toCommandContextInfo_2691_, 6);
v_ngen_2704_ = lean_ctor_get(v_toCommandContextInfo_2691_, 7);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_toCommandContextInfo_2691_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_toCommandContextInfo_2691_, 3);
lean_dec(v_unused_2719_);
v___x_2706_ = v_toCommandContextInfo_2691_;
v_isShared_2707_ = v_isSharedCheck_2718_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_ngen_2704_);
lean_inc(v_openDecls_2703_);
lean_inc(v_currNamespace_2702_);
lean_inc(v_options_2701_);
lean_inc(v_fileMap_2700_);
lean_inc(v_cmdEnv_x3f_2699_);
lean_inc(v_env_2698_);
lean_dec(v_toCommandContextInfo_2691_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2718_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_mctxAfter_2708_; lean_object* v___x_2710_; 
v_mctxAfter_2708_ = lean_ctor_get(v_i_2692_, 3);
lean_inc_ref(v_mctxAfter_2708_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 3, v_mctxAfter_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_env_2698_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_cmdEnv_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_fileMap_2700_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_mctxAfter_2708_);
lean_ctor_set(v_reuseFailAlloc_2717_, 4, v_options_2701_);
lean_ctor_set(v_reuseFailAlloc_2717_, 5, v_currNamespace_2702_);
lean_ctor_set(v_reuseFailAlloc_2717_, 6, v_openDecls_2703_);
lean_ctor_set(v_reuseFailAlloc_2717_, 7, v_ngen_2704_);
v___x_2710_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2712_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2710_);
v___x_2712_ = v___x_2696_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_parentDecl_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_autoImplicits_2694_);
v___x_2712_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2714_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2712_);
v___x_2714_ = v___x_2689_;
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
}
else
{
return v_x_2685_;
}
}
else
{
return v_x_2685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2723_, lean_object* v_x_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2723_, v_x_2724_);
lean_dec_ref(v_x_2724_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2726_, lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
return v_x_2726_;
}
else
{
lean_object* v_head_2728_; lean_object* v_tail_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_head_2728_ = lean_ctor_get(v_x_2727_, 0);
v_tail_2729_ = lean_ctor_get(v_x_2727_, 1);
v___x_2730_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2731_ = lean_string_append(v_x_2726_, v___x_2730_);
v___x_2732_ = lean_expr_dbg_to_string(v_head_2728_);
v___x_2733_ = lean_string_append(v___x_2731_, v___x_2732_);
lean_dec_ref(v___x_2732_);
v_x_2726_ = v___x_2733_;
v_x_2727_ = v_tail_2729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2735_, lean_object* v_x_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2735_, v_x_2736_);
lean_dec(v_x_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2740_){
_start:
{
if (lean_obj_tag(v_x_2740_) == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2741_;
}
else
{
lean_object* v_tail_2742_; 
v_tail_2742_ = lean_ctor_get(v_x_2740_, 1);
if (lean_obj_tag(v_tail_2742_) == 0)
{
lean_object* v_head_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_head_2743_ = lean_ctor_get(v_x_2740_, 0);
v___x_2744_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2745_ = lean_expr_dbg_to_string(v_head_2743_);
v___x_2746_ = lean_string_append(v___x_2744_, v___x_2745_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2748_ = lean_string_append(v___x_2746_, v___x_2747_);
return v___x_2748_;
}
else
{
lean_object* v_head_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint32_t v___x_2754_; lean_object* v___x_2755_; 
v_head_2749_ = lean_ctor_get(v_x_2740_, 0);
v___x_2750_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2751_ = lean_expr_dbg_to_string(v_head_2749_);
v___x_2752_ = lean_string_append(v___x_2750_, v___x_2751_);
lean_dec_ref(v___x_2751_);
v___x_2753_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2752_, v_tail_2742_);
v___x_2754_ = 93;
v___x_2755_ = lean_string_push(v___x_2753_, v___x_2754_);
return v___x_2755_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2756_);
lean_dec(v_x_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2764_){
_start:
{
switch(lean_obj_tag(v_ctx_2764_))
{
case 0:
{
lean_object* v___x_2765_; 
lean_dec_ref_known(v_ctx_2764_, 1);
v___x_2765_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2765_;
}
case 1:
{
lean_object* v_parentDecl_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2779_; 
v_parentDecl_2766_ = lean_ctor_get(v_ctx_2764_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_ctx_2764_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2768_ = v_ctx_2764_;
v_isShared_2769_ = v_isSharedCheck_2779_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_parentDecl_2766_);
lean_dec(v_ctx_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2779_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2770_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2771_ = 1;
v___x_2772_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2766_, v___x_2771_);
v___x_2773_ = lean_string_append(v___x_2770_, v___x_2772_);
lean_dec_ref(v___x_2772_);
v___x_2774_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2775_ = lean_string_append(v___x_2773_, v___x_2774_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 3);
lean_ctor_set(v___x_2768_, 0, v___x_2775_);
v___x_2777_ = v___x_2768_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
default: 
{
lean_object* v_autoImplicits_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2795_; 
v_autoImplicits_2780_ = lean_ctor_get(v_ctx_2764_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_ctx_2764_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2782_ = v_ctx_2764_;
v_isShared_2783_ = v_isSharedCheck_2795_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_autoImplicits_2780_);
lean_dec(v_ctx_2764_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2795_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2784_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2785_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2786_ = lean_array_to_list(v_autoImplicits_2780_);
v___x_2787_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2786_);
lean_dec(v___x_2786_);
v___x_2788_ = lean_string_append(v___x_2785_, v___x_2787_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = lean_string_append(v___x_2784_, v___x_2788_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2791_ = lean_string_append(v___x_2789_, v___x_2790_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 3);
lean_ctor_set(v___x_2782_, 0, v___x_2791_);
v___x_2793_ = v___x_2782_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2805_, lean_object* v_ctx_x3f_2806_){
_start:
{
switch(lean_obj_tag(v_tree_2805_))
{
case 0:
{
lean_object* v_i_2808_; lean_object* v_t_2809_; lean_object* v___x_2810_; 
v_i_2808_ = lean_ctor_get(v_tree_2805_, 0);
lean_inc_ref(v_i_2808_);
v_t_2809_ = lean_ctor_get(v_tree_2805_, 1);
lean_inc_ref(v_t_2809_);
lean_dec_ref_known(v_tree_2805_, 2);
v___x_2810_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2808_, v_ctx_x3f_2806_);
v_tree_2805_ = v_t_2809_;
v_ctx_x3f_2806_ = v___x_2810_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2806_) == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec_ref_known(v_tree_2805_, 2);
v___x_2812_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
else
{
lean_object* v_i_2814_; lean_object* v_children_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2865_; 
v_i_2814_ = lean_ctor_get(v_tree_2805_, 0);
v_children_2815_ = lean_ctor_get(v_tree_2805_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_tree_2805_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2817_ = v_tree_2805_;
v_isShared_2818_ = v_isSharedCheck_2865_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_children_2815_);
lean_inc(v_i_2814_);
lean_dec(v_tree_2805_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2865_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_val_2819_; lean_object* v___x_2820_; 
v_val_2819_ = lean_ctor_get(v_ctx_x3f_2806_, 0);
lean_inc_ref(v_i_2814_);
lean_inc(v_val_2819_);
v___x_2820_ = l_Lean_Elab_Info_format(v_val_2819_, v_i_2814_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2864_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2864_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2864_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_size_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_size_2825_ = lean_ctor_get(v_children_2815_, 2);
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = lean_nat_dec_eq(v_size_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2823_);
v___x_2828_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2806_, v_i_2814_);
lean_dec_ref(v_i_2814_);
v___x_2829_ = l_Lean_PersistentArray_toList___redArg(v_children_2815_);
lean_dec_ref(v_children_2815_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2828_, v___x_2829_, v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2847_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2847_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2847_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2836_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 5);
lean_ctor_set(v___x_2817_, 1, v_a_2821_);
lean_ctor_set(v___x_2817_, 0, v___x_2836_);
v___x_2838_ = v___x_2817_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_a_2821_);
v___x_2838_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2839_ = lean_box(1);
v___x_2840_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2839_, v_a_2832_);
v___x_2841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2838_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Std_Format_nestD(v___x_2841_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2842_);
v___x_2844_ = v___x_2834_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2821_);
lean_del_object(v___x_2817_);
v_a_2848_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2831_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2831_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_dec_ref(v_children_2815_);
lean_dec_ref_known(v_ctx_x3f_2806_, 1);
lean_dec_ref(v_i_2814_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 5);
lean_ctor_set(v___x_2817_, 1, v_a_2821_);
lean_ctor_set(v___x_2817_, 0, v___x_2856_);
v___x_2858_ = v___x_2817_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_a_2821_);
v___x_2858_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2859_ = l_Std_Format_nestD(v___x_2858_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2859_);
v___x_2861_ = v___x_2823_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
else
{
lean_del_object(v___x_2817_);
lean_dec_ref(v_children_2815_);
lean_dec_ref_known(v_ctx_x3f_2806_, 1);
lean_dec_ref(v_i_2814_);
return v___x_2820_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_ctx_x3f_2806_);
v_mvarId_2866_ = lean_ctor_get(v_tree_2805_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_tree_2805_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2868_ = v_tree_2805_;
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_mvarId_2866_);
lean_dec(v_tree_2805_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2870_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2871_ = 1;
v___x_2872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2866_, v___x_2871_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 3);
lean_ctor_set(v___x_2868_, 0, v___x_2872_);
v___x_2874_ = v___x_2868_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2870_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Std_Format_nestD(v___x_2875_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v___x_2880_);
v___x_2884_ = l_List_reverse___redArg(v_x_2882_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
else
{
lean_object* v_head_2886_; lean_object* v_tail_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2905_; 
v_head_2886_ = lean_ctor_get(v_x_2881_, 0);
v_tail_2887_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2889_ = v_x_2881_;
v_isShared_2890_ = v_isSharedCheck_2905_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_tail_2887_);
lean_inc(v_head_2886_);
lean_dec(v_x_2881_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2905_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; 
lean_inc(v___x_2880_);
v___x_2891_ = l_Lean_Elab_InfoTree_format(v_head_2886_, v___x_2880_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v_x_2882_);
lean_ctor_set(v___x_2889_, 0, v_a_2892_);
v___x_2894_ = v___x_2889_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2892_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_x_2882_);
v___x_2894_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v_x_2881_ = v_tail_2887_;
v_x_2882_ = v___x_2894_;
goto _start;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_del_object(v___x_2889_);
lean_dec(v_tail_2887_);
lean_dec(v_x_2882_);
lean_dec(v___x_2880_);
v_a_2897_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2891_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2891_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2906_, v_x_2907_, v_x_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2911_, lean_object* v_ctx_x3f_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Elab_InfoTree_format(v_tree_2911_, v_ctx_x3f_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2915_, lean_object* v_s_2916_){
_start:
{
uint8_t v_enabled_2917_; lean_object* v_assignment_2918_; lean_object* v_lazyAssignment_2919_; lean_object* v_trees_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_enabled_2917_ = lean_ctor_get_uint8(v_s_2916_, sizeof(void*)*3);
v_assignment_2918_ = lean_ctor_get(v_s_2916_, 0);
v_lazyAssignment_2919_ = lean_ctor_get(v_s_2916_, 1);
v_trees_2920_ = lean_ctor_get(v_s_2916_, 2);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_s_2916_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2922_ = v_s_2916_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_trees_2920_);
lean_inc(v_lazyAssignment_2919_);
lean_inc(v_assignment_2918_);
lean_dec(v_s_2916_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = lean_apply_1(v_f_2915_, v_trees_2920_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 2, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_assignment_2918_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_lazyAssignment_2919_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v___x_2924_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*3, v_enabled_2917_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2929_, lean_object* v_f_2930_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2934_, lean_object* v_inst_2935_, lean_object* v_f_2936_){
_start:
{
lean_object* v_modifyInfoState_2937_; lean_object* v___f_2938_; lean_object* v___x_2939_; 
v_modifyInfoState_2937_ = lean_ctor_get(v_inst_2935_, 1);
lean_inc(v_modifyInfoState_2937_);
lean_dec_ref(v_inst_2935_);
v___f_2938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2938_, 0, v_f_2936_);
v___x_2939_ = lean_apply_1(v_modifyInfoState_2937_, v___f_2938_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(32u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2943_ = ((size_t)5ULL);
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_unsigned_to_nat(32u);
v___x_2946_ = lean_mk_empty_array_with_capacity(v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2948_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
lean_ctor_set(v___x_2948_, 2, v___x_2944_);
lean_ctor_set(v___x_2948_, 3, v___x_2944_);
lean_ctor_set_usize(v___x_2948_, 4, v___x_2943_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2949_){
_start:
{
uint8_t v_enabled_2950_; lean_object* v_assignment_2951_; lean_object* v_lazyAssignment_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2960_; 
v_enabled_2950_ = lean_ctor_get_uint8(v_s_2949_, sizeof(void*)*3);
v_assignment_2951_ = lean_ctor_get(v_s_2949_, 0);
v_lazyAssignment_2952_ = lean_ctor_get(v_s_2949_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_s_2949_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_s_2949_, 2);
lean_dec(v_unused_2961_);
v___x_2954_ = v_s_2949_;
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_lazyAssignment_2952_);
lean_inc(v_assignment_2951_);
lean_dec(v_s_2949_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 2, v___x_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_assignment_2951_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_lazyAssignment_2952_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v___x_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*3, v_enabled_2950_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2962_, lean_object* v_trees_2963_, lean_object* v_____r_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_apply_2(v_toPure_2962_, lean_box(0), v_trees_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2966_, lean_object* v_modifyInfoState_2967_, lean_object* v___f_2968_, lean_object* v_toBind_2969_, lean_object* v_____do__lift_2970_){
_start:
{
lean_object* v_trees_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_trees_2971_ = lean_ctor_get(v_____do__lift_2970_, 2);
lean_inc_ref(v_trees_2971_);
lean_dec_ref(v_____do__lift_2970_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2972_, 0, v_toPure_2966_);
lean_closure_set(v___f_2972_, 1, v_trees_2971_);
v___x_2973_ = lean_apply_1(v_modifyInfoState_2967_, v___f_2968_);
v___x_2974_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2973_, v___f_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2976_, lean_object* v_inst_2977_){
_start:
{
lean_object* v_toApplicative_2978_; lean_object* v_toBind_2979_; lean_object* v_getInfoState_2980_; lean_object* v_modifyInfoState_2981_; lean_object* v_toPure_2982_; lean_object* v___f_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; 
v_toApplicative_2978_ = lean_ctor_get(v_inst_2976_, 0);
lean_inc_ref(v_toApplicative_2978_);
v_toBind_2979_ = lean_ctor_get(v_inst_2976_, 1);
lean_inc_n(v_toBind_2979_, 2);
lean_dec_ref(v_inst_2976_);
v_getInfoState_2980_ = lean_ctor_get(v_inst_2977_, 0);
lean_inc(v_getInfoState_2980_);
v_modifyInfoState_2981_ = lean_ctor_get(v_inst_2977_, 1);
lean_inc(v_modifyInfoState_2981_);
lean_dec_ref(v_inst_2977_);
v_toPure_2982_ = lean_ctor_get(v_toApplicative_2978_, 1);
lean_inc(v_toPure_2982_);
lean_dec_ref(v_toApplicative_2978_);
v___f_2983_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2984_, 0, v_toPure_2982_);
lean_closure_set(v___f_2984_, 1, v_modifyInfoState_2981_);
lean_closure_set(v___f_2984_, 2, v___f_2983_);
lean_closure_set(v___f_2984_, 3, v_toBind_2979_);
v___x_2985_ = lean_apply_4(v_toBind_2979_, lean_box(0), lean_box(0), v_getInfoState_2980_, v___f_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2987_, v_inst_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2990_, lean_object* v_s_2991_){
_start:
{
uint8_t v_enabled_2992_; lean_object* v_assignment_2993_; lean_object* v_lazyAssignment_2994_; lean_object* v_trees_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3003_; 
v_enabled_2992_ = lean_ctor_get_uint8(v_s_2991_, sizeof(void*)*3);
v_assignment_2993_ = lean_ctor_get(v_s_2991_, 0);
v_lazyAssignment_2994_ = lean_ctor_get(v_s_2991_, 1);
v_trees_2995_ = lean_ctor_get(v_s_2991_, 2);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_s_2991_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2997_ = v_s_2991_;
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_trees_2995_);
lean_inc(v_lazyAssignment_2994_);
lean_inc(v_assignment_2993_);
lean_dec(v_s_2991_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = l_Lean_PersistentArray_push___redArg(v_trees_2995_, v_t_2990_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 2, v___x_2999_);
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_assignment_2993_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_lazyAssignment_2994_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v___x_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3002_, sizeof(void*)*3, v_enabled_2992_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_3004_, lean_object* v_modifyInfoState_3005_, lean_object* v___f_3006_, lean_object* v_____do__lift_3007_){
_start:
{
uint8_t v_enabled_3008_; 
v_enabled_3008_ = lean_ctor_get_uint8(v_____do__lift_3007_, sizeof(void*)*3);
if (v_enabled_3008_ == 0)
{
lean_object* v_toPure_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v___f_3006_);
lean_dec(v_modifyInfoState_3005_);
v_toPure_3009_ = lean_ctor_get(v_toApplicative_3004_, 1);
lean_inc(v_toPure_3009_);
lean_dec_ref(v_toApplicative_3004_);
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_apply_2(v_toPure_3009_, lean_box(0), v___x_3010_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; 
lean_dec_ref(v_toApplicative_3004_);
v___x_3012_ = lean_apply_1(v_modifyInfoState_3005_, v___f_3006_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_3013_, lean_object* v_modifyInfoState_3014_, lean_object* v___f_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_3013_, v_modifyInfoState_3014_, v___f_3015_, v_____do__lift_3016_);
lean_dec_ref(v_____do__lift_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_t_3020_){
_start:
{
lean_object* v_toApplicative_3021_; lean_object* v_toBind_3022_; lean_object* v_getInfoState_3023_; lean_object* v_modifyInfoState_3024_; lean_object* v___f_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; 
v_toApplicative_3021_ = lean_ctor_get(v_inst_3018_, 0);
lean_inc_ref(v_toApplicative_3021_);
v_toBind_3022_ = lean_ctor_get(v_inst_3018_, 1);
lean_inc(v_toBind_3022_);
lean_dec_ref(v_inst_3018_);
v_getInfoState_3023_ = lean_ctor_get(v_inst_3019_, 0);
lean_inc(v_getInfoState_3023_);
v_modifyInfoState_3024_ = lean_ctor_get(v_inst_3019_, 1);
lean_inc(v_modifyInfoState_3024_);
lean_dec_ref(v_inst_3019_);
v___f_3025_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3025_, 0, v_t_3020_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3026_, 0, v_toApplicative_3021_);
lean_closure_set(v___f_3026_, 1, v_modifyInfoState_3024_);
lean_closure_set(v___f_3026_, 2, v___f_3025_);
v___x_3027_ = lean_apply_4(v_toBind_3022_, lean_box(0), lean_box(0), v_getInfoState_3023_, v___f_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_t_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3029_, v_inst_3030_, v_t_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_3033_, lean_object* v_t_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_____do__lift_3037_){
_start:
{
uint8_t v_enabled_3038_; 
v_enabled_3038_ = lean_ctor_get_uint8(v_____do__lift_3037_, sizeof(void*)*3);
if (v_enabled_3038_ == 0)
{
lean_object* v_toPure_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v_inst_3036_);
lean_dec_ref(v_inst_3035_);
lean_dec_ref(v_t_3034_);
v_toPure_3039_ = lean_ctor_get(v_toApplicative_3033_, 1);
lean_inc(v_toPure_3039_);
lean_dec_ref(v_toApplicative_3033_);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_apply_2(v_toPure_3039_, lean_box(0), v___x_3040_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_toApplicative_3033_);
v___x_3042_ = lean_unsigned_to_nat(32u);
v___x_3043_ = lean_mk_empty_array_with_capacity(v___x_3042_);
lean_dec_ref(v___x_3043_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_t_3034_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3035_, v_inst_3036_, v___x_3045_);
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_3047_, lean_object* v_t_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_____do__lift_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_3047_, v_t_3048_, v_inst_3049_, v_inst_3050_, v_____do__lift_3051_);
lean_dec_ref(v_____do__lift_3051_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_t_3055_){
_start:
{
lean_object* v_toApplicative_3056_; lean_object* v_toBind_3057_; lean_object* v_getInfoState_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; 
v_toApplicative_3056_ = lean_ctor_get(v_inst_3053_, 0);
lean_inc_ref(v_toApplicative_3056_);
v_toBind_3057_ = lean_ctor_get(v_inst_3053_, 1);
lean_inc(v_toBind_3057_);
v_getInfoState_3058_ = lean_ctor_get(v_inst_3054_, 0);
lean_inc(v_getInfoState_3058_);
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3059_, 0, v_toApplicative_3056_);
lean_closure_set(v___f_3059_, 1, v_t_3055_);
lean_closure_set(v___f_3059_, 2, v_inst_3053_);
lean_closure_set(v___f_3059_, 3, v_inst_3054_);
v___x_3060_ = lean_apply_4(v_toBind_3057_, lean_box(0), lean_box(0), v_getInfoState_3058_, v___f_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_t_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3062_, v_inst_3063_, v_t_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_info_3068_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_info_3068_);
v___x_3070_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3066_, v_inst_3067_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_info_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3072_, v_inst_3073_, v_info_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3076_, lean_object* v_expectedType_x3f_3077_, lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_____do__lift_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v_stx_3076_);
v___x_3083_ = l_Lean_LocalContext_empty;
v___x_3084_ = 0;
v___x_3085_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3085_, 0, v___x_3082_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
lean_ctor_set(v___x_3085_, 2, v_expectedType_x3f_3077_);
lean_ctor_set(v___x_3085_, 3, v_____do__lift_3080_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*4, v___x_3084_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*4 + 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3078_, v_inst_3079_, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_stx_3092_, lean_object* v_n_3093_, lean_object* v_expectedType_x3f_3094_){
_start:
{
lean_object* v_toBind_3095_; lean_object* v___f_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_toBind_3095_ = lean_ctor_get(v_inst_3088_, 1);
lean_inc(v_toBind_3095_);
lean_inc_ref(v_inst_3088_);
v___f_3096_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3096_, 0, v_stx_3092_);
lean_closure_set(v___f_3096_, 1, v_expectedType_x3f_3094_);
lean_closure_set(v___f_3096_, 2, v_inst_3088_);
lean_closure_set(v___f_3096_, 3, v_inst_3089_);
v___x_3097_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3088_, v_inst_3090_, v_inst_3091_, v_n_3093_);
v___x_3098_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v___x_3097_, v___f_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_stx_3104_, lean_object* v_n_3105_, lean_object* v_expectedType_x3f_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3100_, v_inst_3101_, v_inst_3102_, v_inst_3103_, v_stx_3104_, v_n_3105_, v_expectedType_x3f_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; lean_object* v_infoState_3112_; uint8_t v_enabled_3113_; 
v___x_3111_ = lean_st_ref_get(v___y_3109_);
v_infoState_3112_ = lean_ctor_get(v___x_3111_, 7);
lean_inc_ref(v_infoState_3112_);
lean_dec(v___x_3111_);
v_enabled_3113_ = lean_ctor_get_uint8(v_infoState_3112_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3112_);
if (v_enabled_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v_t_3108_);
v___x_3114_ = lean_box(0);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
else
{
lean_object* v___x_3116_; lean_object* v_infoState_3117_; lean_object* v_env_3118_; lean_object* v_nextMacroScope_3119_; lean_object* v_ngen_3120_; lean_object* v_auxDeclNGen_3121_; lean_object* v_traceState_3122_; lean_object* v_cache_3123_; lean_object* v_messages_3124_; lean_object* v_snapshotTasks_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3147_; 
v___x_3116_ = lean_st_ref_take(v___y_3109_);
v_infoState_3117_ = lean_ctor_get(v___x_3116_, 7);
v_env_3118_ = lean_ctor_get(v___x_3116_, 0);
v_nextMacroScope_3119_ = lean_ctor_get(v___x_3116_, 1);
v_ngen_3120_ = lean_ctor_get(v___x_3116_, 2);
v_auxDeclNGen_3121_ = lean_ctor_get(v___x_3116_, 3);
v_traceState_3122_ = lean_ctor_get(v___x_3116_, 4);
v_cache_3123_ = lean_ctor_get(v___x_3116_, 5);
v_messages_3124_ = lean_ctor_get(v___x_3116_, 6);
v_snapshotTasks_3125_ = lean_ctor_get(v___x_3116_, 8);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3127_ = v___x_3116_;
v_isShared_3128_ = v_isSharedCheck_3147_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_snapshotTasks_3125_);
lean_inc(v_infoState_3117_);
lean_inc(v_messages_3124_);
lean_inc(v_cache_3123_);
lean_inc(v_traceState_3122_);
lean_inc(v_auxDeclNGen_3121_);
lean_inc(v_ngen_3120_);
lean_inc(v_nextMacroScope_3119_);
lean_inc(v_env_3118_);
lean_dec(v___x_3116_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3147_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
uint8_t v_enabled_3129_; lean_object* v_assignment_3130_; lean_object* v_lazyAssignment_3131_; lean_object* v_trees_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3146_; 
v_enabled_3129_ = lean_ctor_get_uint8(v_infoState_3117_, sizeof(void*)*3);
v_assignment_3130_ = lean_ctor_get(v_infoState_3117_, 0);
v_lazyAssignment_3131_ = lean_ctor_get(v_infoState_3117_, 1);
v_trees_3132_ = lean_ctor_get(v_infoState_3117_, 2);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_infoState_3117_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3134_ = v_infoState_3117_;
v_isShared_3135_ = v_isSharedCheck_3146_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_trees_3132_);
lean_inc(v_lazyAssignment_3131_);
lean_inc(v_assignment_3130_);
lean_dec(v_infoState_3117_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3146_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = l_Lean_PersistentArray_push___redArg(v_trees_3132_, v_t_3108_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 2, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_assignment_3130_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_lazyAssignment_3131_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v___x_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, sizeof(void*)*3, v_enabled_3129_);
v___x_3138_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 7, v___x_3138_);
v___x_3140_ = v___x_3127_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_env_3118_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_nextMacroScope_3119_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_ngen_3120_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_auxDeclNGen_3121_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_traceState_3122_);
lean_ctor_set(v_reuseFailAlloc_3144_, 5, v_cache_3123_);
lean_ctor_set(v_reuseFailAlloc_3144_, 6, v_messages_3124_);
lean_ctor_set(v_reuseFailAlloc_3144_, 7, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3144_, 8, v_snapshotTasks_3125_);
v___x_3140_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_st_ref_set(v___y_3109_, v___x_3140_);
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3148_, v___y_3149_);
lean_dec(v___y_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v_infoState_3157_; uint8_t v_enabled_3158_; 
v___x_3156_ = lean_st_ref_get(v___y_3154_);
v_infoState_3157_ = lean_ctor_get(v___x_3156_, 7);
lean_inc_ref(v_infoState_3157_);
lean_dec(v___x_3156_);
v_enabled_3158_ = lean_ctor_get_uint8(v_infoState_3157_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3157_);
if (v_enabled_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref(v_t_3152_);
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3161_ = lean_unsigned_to_nat(32u);
v___x_3162_ = lean_mk_empty_array_with_capacity(v___x_3161_);
lean_dec_ref(v___x_3162_);
v___x_3163_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_t_3152_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3164_, v___y_3154_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3170_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
lean_ctor_set(v___x_3176_, 2, v___x_3175_);
lean_ctor_set(v___x_3176_, 3, v___x_3175_);
lean_ctor_set(v___x_3176_, 4, v___x_3174_);
lean_ctor_set(v___x_3176_, 5, v___x_3174_);
lean_ctor_set(v___x_3176_, 6, v___x_3174_);
lean_ctor_set(v___x_3176_, 7, v___x_3174_);
lean_ctor_set(v___x_3176_, 8, v___x_3174_);
lean_ctor_set(v___x_3176_, 9, v___x_3174_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3177_ = lean_box(1);
v___x_3178_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v___x_3178_);
lean_ctor_set(v___x_3180_, 2, v___x_3177_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3202_, lean_object* v_declHint_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; lean_object* v_env_3207_; uint8_t v___x_3208_; 
v___x_3206_ = lean_st_ref_get(v___y_3204_);
v_env_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc_ref(v_env_3207_);
lean_dec(v___x_3206_);
v___x_3208_ = l_Lean_Name_isAnonymous(v_declHint_3203_);
if (v___x_3208_ == 0)
{
uint8_t v_isExporting_3209_; 
v_isExporting_3209_ = lean_ctor_get_uint8(v_env_3207_, sizeof(void*)*8);
if (v_isExporting_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec_ref(v_env_3207_);
lean_dec(v_declHint_3203_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_msg_3202_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; uint8_t v___x_3212_; 
lean_inc_ref(v_env_3207_);
v___x_3211_ = l_Lean_Environment_setExporting(v_env_3207_, v___x_3208_);
lean_inc(v_declHint_3203_);
lean_inc_ref(v___x_3211_);
v___x_3212_ = l_Lean_Environment_contains(v___x_3211_, v_declHint_3203_, v_isExporting_3209_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v___x_3211_);
lean_dec_ref(v_env_3207_);
lean_dec(v_declHint_3203_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v_msg_3202_);
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v_c_3219_; lean_object* v___x_3220_; 
v___x_3214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3216_ = l_Lean_Options_empty;
v___x_3217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3211_);
lean_ctor_set(v___x_3217_, 1, v___x_3214_);
lean_ctor_set(v___x_3217_, 2, v___x_3215_);
lean_ctor_set(v___x_3217_, 3, v___x_3216_);
lean_inc(v_declHint_3203_);
v___x_3218_ = l_Lean_MessageData_ofConstName(v_declHint_3203_, v___x_3208_);
v_c_3219_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3219_, 0, v___x_3217_);
lean_ctor_set(v_c_3219_, 1, v___x_3218_);
v___x_3220_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3207_, v_declHint_3203_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref(v_env_3207_);
lean_dec(v_declHint_3203_);
v___x_3221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v_c_3219_);
v___x_3223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_MessageData_note(v___x_3224_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_msg_3202_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
else
{
lean_object* v_val_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3263_; 
v_val_3228_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3230_ = v___x_3220_;
v_isShared_3231_ = v_isSharedCheck_3263_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_val_3228_);
lean_dec(v___x_3220_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3263_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_mod_3235_; uint8_t v___x_3236_; 
v___x_3232_ = lean_box(0);
v___x_3233_ = l_Lean_Environment_header(v_env_3207_);
lean_dec_ref(v_env_3207_);
v___x_3234_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3233_);
v_mod_3235_ = lean_array_get(v___x_3232_, v___x_3234_, v_val_3228_);
lean_dec(v_val_3228_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = l_Lean_isPrivateName(v_declHint_3203_);
lean_dec(v_declHint_3203_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v_c_3219_);
v___x_3239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = l_Lean_MessageData_ofName(v_mod_3235_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = l_Lean_MessageData_note(v___x_3244_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_msg_3202_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3246_);
v___x_3248_ = v___x_3230_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v_c_3219_);
v___x_3252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_MessageData_ofName(v_mod_3235_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Lean_MessageData_note(v___x_3257_);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v_msg_3202_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3259_);
v___x_3261_ = v___x_3230_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3264_; 
lean_dec_ref(v_env_3207_);
lean_dec(v_declHint_3203_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_msg_3202_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3265_, lean_object* v_declHint_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3265_, v_declHint_3266_, v___y_3267_);
lean_dec(v___y_3267_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3270_, lean_object* v_declHint_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3285_; 
v___x_3275_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3270_, v_declHint_3271_, v___y_3273_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3285_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3285_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3280_ = l_Lean_unknownIdentifierMessageTag;
v___x_3281_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v_a_3276_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3281_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3286_, lean_object* v_declHint_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3286_, v_declHint_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___x_3296_; lean_object* v_env_3297_; lean_object* v_options_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3296_ = lean_st_ref_get(v___y_3294_);
v_env_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc_ref(v_env_3297_);
lean_dec(v___x_3296_);
v_options_3298_ = lean_ctor_get(v___y_3293_, 2);
v___x_3299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3300_ = lean_unsigned_to_nat(32u);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3300_);
lean_dec_ref(v___x_3301_);
v___x_3302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3298_);
v___x_3303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3303_, 0, v_env_3297_);
lean_ctor_set(v___x_3303_, 1, v___x_3299_);
lean_ctor_set(v___x_3303_, 2, v___x_3302_);
lean_ctor_set(v___x_3303_, 3, v_options_3298_);
v___x_3304_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v_msgData_3292_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_ref_3315_; lean_object* v___x_3316_; lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3325_; 
v_ref_3315_ = lean_ctor_get(v___y_3312_, 5);
v___x_3316_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3311_, v___y_3312_, v___y_3313_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_inc(v_ref_3315_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_ref_3315_);
lean_ctor_set(v___x_3321_, 1, v_a_3317_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 1);
lean_ctor_set(v___x_3319_, 0, v___x_3321_);
v___x_3323_ = v___x_3319_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3331_, lean_object* v_msg_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_fileName_3336_; lean_object* v_fileMap_3337_; lean_object* v_options_3338_; lean_object* v_currRecDepth_3339_; lean_object* v_maxRecDepth_3340_; lean_object* v_ref_3341_; lean_object* v_currNamespace_3342_; lean_object* v_openDecls_3343_; lean_object* v_initHeartbeats_3344_; lean_object* v_maxHeartbeats_3345_; lean_object* v_quotContext_3346_; lean_object* v_currMacroScope_3347_; uint8_t v_diag_3348_; lean_object* v_cancelTk_x3f_3349_; uint8_t v_suppressElabErrors_3350_; lean_object* v_inheritedTraceOptions_3351_; lean_object* v_ref_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_fileName_3336_ = lean_ctor_get(v___y_3333_, 0);
v_fileMap_3337_ = lean_ctor_get(v___y_3333_, 1);
v_options_3338_ = lean_ctor_get(v___y_3333_, 2);
v_currRecDepth_3339_ = lean_ctor_get(v___y_3333_, 3);
v_maxRecDepth_3340_ = lean_ctor_get(v___y_3333_, 4);
v_ref_3341_ = lean_ctor_get(v___y_3333_, 5);
v_currNamespace_3342_ = lean_ctor_get(v___y_3333_, 6);
v_openDecls_3343_ = lean_ctor_get(v___y_3333_, 7);
v_initHeartbeats_3344_ = lean_ctor_get(v___y_3333_, 8);
v_maxHeartbeats_3345_ = lean_ctor_get(v___y_3333_, 9);
v_quotContext_3346_ = lean_ctor_get(v___y_3333_, 10);
v_currMacroScope_3347_ = lean_ctor_get(v___y_3333_, 11);
v_diag_3348_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*14);
v_cancelTk_x3f_3349_ = lean_ctor_get(v___y_3333_, 12);
v_suppressElabErrors_3350_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3351_ = lean_ctor_get(v___y_3333_, 13);
v_ref_3352_ = l_Lean_replaceRef(v_ref_3331_, v_ref_3341_);
lean_inc_ref(v_inheritedTraceOptions_3351_);
lean_inc(v_cancelTk_x3f_3349_);
lean_inc(v_currMacroScope_3347_);
lean_inc(v_quotContext_3346_);
lean_inc(v_maxHeartbeats_3345_);
lean_inc(v_initHeartbeats_3344_);
lean_inc(v_openDecls_3343_);
lean_inc(v_currNamespace_3342_);
lean_inc(v_maxRecDepth_3340_);
lean_inc(v_currRecDepth_3339_);
lean_inc_ref(v_options_3338_);
lean_inc_ref(v_fileMap_3337_);
lean_inc_ref(v_fileName_3336_);
v___x_3353_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3353_, 0, v_fileName_3336_);
lean_ctor_set(v___x_3353_, 1, v_fileMap_3337_);
lean_ctor_set(v___x_3353_, 2, v_options_3338_);
lean_ctor_set(v___x_3353_, 3, v_currRecDepth_3339_);
lean_ctor_set(v___x_3353_, 4, v_maxRecDepth_3340_);
lean_ctor_set(v___x_3353_, 5, v_ref_3352_);
lean_ctor_set(v___x_3353_, 6, v_currNamespace_3342_);
lean_ctor_set(v___x_3353_, 7, v_openDecls_3343_);
lean_ctor_set(v___x_3353_, 8, v_initHeartbeats_3344_);
lean_ctor_set(v___x_3353_, 9, v_maxHeartbeats_3345_);
lean_ctor_set(v___x_3353_, 10, v_quotContext_3346_);
lean_ctor_set(v___x_3353_, 11, v_currMacroScope_3347_);
lean_ctor_set(v___x_3353_, 12, v_cancelTk_x3f_3349_);
lean_ctor_set(v___x_3353_, 13, v_inheritedTraceOptions_3351_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*14, v_diag_3348_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*14 + 1, v_suppressElabErrors_3350_);
v___x_3354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3332_, v___x_3353_, v___y_3334_);
lean_dec_ref_known(v___x_3353_, 14);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3355_, lean_object* v_msg_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3355_, v_msg_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v_ref_3355_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3361_, lean_object* v_msg_3362_, lean_object* v_declHint_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v_a_3368_; lean_object* v___x_3369_; 
v___x_3367_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3362_, v_declHint_3363_, v___y_3364_, v___y_3365_);
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3361_, v_a_3368_, v___y_3364_, v___y_3365_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3370_, lean_object* v_msg_3371_, lean_object* v_declHint_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3370_, v_msg_3371_, v_declHint_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v_ref_3370_);
return v_res_3376_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3379_ = l_Lean_stringToMessageData(v___x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3383_, lean_object* v_constName_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3388_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3389_ = 0;
lean_inc(v_constName_3384_);
v___x_3390_ = l_Lean_MessageData_ofConstName(v_constName_3384_, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3388_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3383_, v___x_3393_, v_constName_3384_, v___y_3385_, v___y_3386_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3395_, lean_object* v_constName_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3395_, v_constName_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v_ref_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_ref_3405_; lean_object* v___x_3406_; 
v_ref_3405_ = lean_ctor_get(v___y_3402_, 5);
v___x_3406_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3405_, v_constName_3401_, v___y_3402_, v___y_3403_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; lean_object* v_env_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; 
v___x_3416_ = lean_st_ref_get(v___y_3414_);
v_env_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc_ref(v_env_3417_);
lean_dec(v___x_3416_);
v___x_3418_ = 0;
lean_inc(v_constName_3412_);
v___x_3419_ = l_Lean_Environment_findConstVal_x3f(v_env_3417_, v_constName_3412_, v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3412_, v___y_3413_, v___y_3414_);
return v___x_3420_;
}
else
{
lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_constName_3412_);
v_val_3421_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3419_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v___x_3419_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_val_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
if (lean_obj_tag(v_a_3434_) == 0)
{
lean_object* v___x_3436_; 
v___x_3436_ = l_List_reverse___redArg(v_a_3435_);
return v___x_3436_;
}
else
{
lean_object* v_head_3437_; lean_object* v_tail_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3447_; 
v_head_3437_ = lean_ctor_get(v_a_3434_, 0);
v_tail_3438_ = lean_ctor_get(v_a_3434_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_a_3434_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3440_ = v_a_3434_;
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_tail_3438_);
lean_inc(v_head_3437_);
lean_dec(v_a_3434_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = l_Lean_mkLevelParam(v_head_3437_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v_a_3435_);
lean_ctor_set(v___x_3440_, 0, v___x_3442_);
v___x_3444_ = v___x_3440_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_a_3435_);
v___x_3444_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3434_ = v_tail_3438_;
v_a_3435_ = v___x_3444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
lean_inc(v_constName_3448_);
v___x_3452_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3464_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v_levelParams_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v_levelParams_3457_ = lean_ctor_get(v_a_3453_, 1);
lean_inc(v_levelParams_3457_);
lean_dec(v_a_3453_);
v___x_3458_ = lean_box(0);
v___x_3459_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3457_, v___x_3458_);
v___x_3460_ = l_Lean_mkConst(v_constName_3448_, v___x_3459_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3460_);
v___x_3462_ = v___x_3455_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_constName_3448_);
v_a_3465_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3452_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3452_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3478_, lean_object* v_n_3479_, lean_object* v_expectedType_x3f_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3479_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v_stx_3478_);
v___x_3488_ = l_Lean_LocalContext_empty;
v___x_3489_ = 0;
v___x_3490_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3490_, 0, v___x_3487_);
lean_ctor_set(v___x_3490_, 1, v___x_3488_);
lean_ctor_set(v___x_3490_, 2, v_expectedType_x3f_3480_);
lean_ctor_set(v___x_3490_, 3, v_a_3485_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*4, v___x_3489_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*4 + 1, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
v___x_3492_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3491_, v___y_3481_, v___y_3482_);
return v___x_3492_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_expectedType_x3f_3480_);
lean_dec(v_stx_3478_);
v_a_3493_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3484_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3484_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3501_, lean_object* v_n_3502_, lean_object* v_expectedType_x3f_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3501_, v_n_3502_, v_expectedType_x3f_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3508_, lean_object* v_expectedType_x3f_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v___x_3513_; 
lean_inc(v_id_3508_);
v___x_3513_ = l_Lean_realizeGlobalConstNoOverload(v_id_3508_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3541_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3541_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3541_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v_infoState_3519_; uint8_t v_enabled_3520_; 
v___x_3518_ = lean_st_ref_get(v_a_3511_);
v_infoState_3519_ = lean_ctor_get(v___x_3518_, 7);
lean_inc_ref(v_infoState_3519_);
lean_dec(v___x_3518_);
v_enabled_3520_ = lean_ctor_get_uint8(v_infoState_3519_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3519_);
if (v_enabled_3520_ == 0)
{
lean_object* v___x_3522_; 
lean_dec(v_expectedType_x3f_3509_);
lean_dec(v_id_3508_);
if (v_isShared_3517_ == 0)
{
v___x_3522_ = v___x_3516_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3514_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
else
{
lean_object* v___x_3524_; 
lean_del_object(v___x_3516_);
lean_inc(v_a_3514_);
v___x_3524_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3508_, v_a_3514_, v_expectedType_x3f_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v___x_3524_, 0);
lean_dec(v_unused_3532_);
v___x_3526_ = v___x_3524_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v___x_3524_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v_a_3514_);
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3514_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_a_3514_);
v_a_3533_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3524_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3524_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3509_);
lean_dec(v_id_3508_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3542_, lean_object* v_expectedType_x3f_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3542_, v_expectedType_x3f_3543_, v_a_3544_, v_a_3545_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3548_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3558_, lean_object* v_constName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3559_, v___y_3560_, v___y_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3564_, lean_object* v_constName_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3564_, v_constName_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3570_, lean_object* v_ref_3571_, lean_object* v_constName_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3571_, v_constName_3572_, v___y_3573_, v___y_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_ref_3578_, lean_object* v_constName_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3577_, v_ref_3578_, v_constName_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v_ref_3578_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3584_, lean_object* v_ref_3585_, lean_object* v_msg_3586_, lean_object* v_declHint_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3585_, v_msg_3586_, v_declHint_3587_, v___y_3588_, v___y_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_ref_3593_, lean_object* v_msg_3594_, lean_object* v_declHint_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3592_, v_ref_3593_, v_msg_3594_, v_declHint_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v_ref_3593_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3600_, lean_object* v_declHint_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3600_, v_declHint_3601_, v___y_3603_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3606_, lean_object* v_declHint_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3606_, v_declHint_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3612_, lean_object* v_ref_3613_, lean_object* v_msg_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3613_, v_msg_3614_, v___y_3615_, v___y_3616_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3619_, lean_object* v_ref_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3619_, v_ref_3620_, v_msg_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v_ref_3620_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3626_, lean_object* v_msg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3627_, v___y_3628_, v___y_3629_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3632_, lean_object* v_msg_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3632_, v_msg_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3638_, lean_object* v_expectedType_x3f_3639_, lean_object* v_as_x27_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
if (lean_obj_tag(v_as_x27_3640_) == 0)
{
lean_object* v___x_3645_; 
lean_dec(v_expectedType_x3f_3639_);
lean_dec(v_id_3638_);
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v_b_3641_);
return v___x_3645_;
}
else
{
lean_object* v_head_3646_; lean_object* v_tail_3647_; lean_object* v___x_3648_; 
v_head_3646_ = lean_ctor_get(v_as_x27_3640_, 0);
v_tail_3647_ = lean_ctor_get(v_as_x27_3640_, 1);
lean_inc(v_expectedType_x3f_3639_);
lean_inc(v_head_3646_);
lean_inc(v_id_3638_);
v___x_3648_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3638_, v_head_3646_, v_expectedType_x3f_3639_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref_known(v___x_3648_, 1);
v___x_3649_ = lean_box(0);
v_as_x27_3640_ = v_tail_3647_;
v_b_3641_ = v___x_3649_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_3639_);
lean_dec(v_id_3638_);
return v___x_3648_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3651_, lean_object* v_expectedType_x3f_3652_, lean_object* v_as_x27_3653_, lean_object* v_b_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3651_, v_expectedType_x3f_3652_, v_as_x27_3653_, v_b_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v_as_x27_3653_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3659_, lean_object* v_expectedType_x3f_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___x_3664_; 
lean_inc(v_id_3659_);
v___x_3664_ = l_Lean_realizeGlobalConst(v_id_3659_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3693_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3693_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3693_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v_infoState_3670_; uint8_t v_enabled_3671_; 
v___x_3669_ = lean_st_ref_get(v_a_3662_);
v_infoState_3670_ = lean_ctor_get(v___x_3669_, 7);
lean_inc_ref(v_infoState_3670_);
lean_dec(v___x_3669_);
v_enabled_3671_ = lean_ctor_get_uint8(v_infoState_3670_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3670_);
if (v_enabled_3671_ == 0)
{
lean_object* v___x_3673_; 
lean_dec(v_expectedType_x3f_3660_);
lean_dec(v_id_3659_);
if (v_isShared_3668_ == 0)
{
v___x_3673_ = v___x_3667_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3665_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_del_object(v___x_3667_);
v___x_3675_ = lean_box(0);
v___x_3676_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3659_, v_expectedType_x3f_3660_, v_a_3665_, v___x_3675_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3684_);
v___x_3678_ = v___x_3676_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v___x_3676_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_a_3665_);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3665_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3665_);
v_a_3685_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3676_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3676_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3660_);
lean_dec(v_id_3659_);
return v___x_3664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3694_, lean_object* v_expectedType_x3f_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3694_, v_expectedType_x3f_3695_, v_a_3696_, v_a_3697_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3700_, lean_object* v_expectedType_x3f_3701_, lean_object* v_as_3702_, lean_object* v_as_x27_3703_, lean_object* v_b_3704_, lean_object* v_a_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3700_, v_expectedType_x3f_3701_, v_as_x27_3703_, v_b_3704_, v___y_3706_, v___y_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3710_, lean_object* v_expectedType_x3f_3711_, lean_object* v_as_3712_, lean_object* v_as_x27_3713_, lean_object* v_b_3714_, lean_object* v_a_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3710_, v_expectedType_x3f_3711_, v_as_3712_, v_as_x27_3713_, v_b_3714_, v_a_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v_as_x27_3713_);
lean_dec(v_as_3712_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3720_, lean_object* v_as_x27_3721_, lean_object* v_b_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
if (lean_obj_tag(v_as_x27_3721_) == 0)
{
lean_object* v___x_3726_; 
lean_dec(v_ref_3720_);
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_b_3722_);
return v___x_3726_;
}
else
{
lean_object* v_head_3727_; lean_object* v_tail_3728_; lean_object* v_fst_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_head_3727_ = lean_ctor_get(v_as_x27_3721_, 0);
v_tail_3728_ = lean_ctor_get(v_as_x27_3721_, 1);
v_fst_3729_ = lean_ctor_get(v_head_3727_, 0);
v___x_3730_ = lean_box(0);
lean_inc(v_fst_3729_);
lean_inc(v_ref_3720_);
v___x_3731_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3720_, v_fst_3729_, v___x_3730_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v___x_3732_; 
lean_dec_ref_known(v___x_3731_, 1);
v___x_3732_ = lean_box(0);
v_as_x27_3721_ = v_tail_3728_;
v_b_3722_ = v___x_3732_;
goto _start;
}
else
{
lean_dec(v_ref_3720_);
return v___x_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3734_, lean_object* v_as_x27_3735_, lean_object* v_b_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3734_, v_as_x27_3735_, v_b_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v_as_x27_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3741_, lean_object* v_id_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_realizeGlobalName(v_id_3742_, v_a_3743_, v_a_3744_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3775_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3775_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3775_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v_infoState_3752_; uint8_t v_enabled_3753_; 
v___x_3751_ = lean_st_ref_get(v_a_3744_);
v_infoState_3752_ = lean_ctor_get(v___x_3751_, 7);
lean_inc_ref(v_infoState_3752_);
lean_dec(v___x_3751_);
v_enabled_3753_ = lean_ctor_get_uint8(v_infoState_3752_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3752_);
if (v_enabled_3753_ == 0)
{
lean_object* v___x_3755_; 
lean_dec(v_ref_3741_);
if (v_isShared_3750_ == 0)
{
v___x_3755_ = v___x_3749_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3747_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_del_object(v___x_3749_);
v___x_3757_ = lean_box(0);
v___x_3758_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3741_, v_a_3747_, v___x_3757_, v_a_3743_, v_a_3744_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v___x_3758_, 0);
lean_dec(v_unused_3766_);
v___x_3760_ = v___x_3758_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_dec(v___x_3758_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v_a_3747_);
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3747_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3747_);
v_a_3767_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3758_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3758_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_3741_);
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3776_, lean_object* v_id_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3776_, v_id_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3782_, lean_object* v_as_3783_, lean_object* v_as_x27_3784_, lean_object* v_b_3785_, lean_object* v_a_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3782_, v_as_x27_3784_, v_b_3785_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3791_, lean_object* v_as_3792_, lean_object* v_as_x27_3793_, lean_object* v_b_3794_, lean_object* v_a_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3791_, v_as_3792_, v_as_x27_3793_, v_b_3794_, v_a_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_as_x27_3793_);
lean_dec(v_as_3792_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3800_){
_start:
{
lean_object* v_fst_3801_; 
v_fst_3801_ = lean_ctor_get(v_self_3800_, 0);
lean_inc(v_fst_3801_);
return v_fst_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3802_);
lean_dec_ref(v_self_3802_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3804_, lean_object* v_treesSaved_3805_, lean_object* v_s_3806_){
_start:
{
if (lean_obj_tag(v_info_3804_) == 0)
{
uint8_t v_enabled_3807_; lean_object* v_assignment_3808_; lean_object* v_lazyAssignment_3809_; lean_object* v_trees_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3820_; 
v_enabled_3807_ = lean_ctor_get_uint8(v_s_3806_, sizeof(void*)*3);
v_assignment_3808_ = lean_ctor_get(v_s_3806_, 0);
v_lazyAssignment_3809_ = lean_ctor_get(v_s_3806_, 1);
v_trees_3810_ = lean_ctor_get(v_s_3806_, 2);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_s_3806_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3812_ = v_s_3806_;
v_isShared_3813_ = v_isSharedCheck_3820_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_trees_3810_);
lean_inc(v_lazyAssignment_3809_);
lean_inc(v_assignment_3808_);
lean_dec(v_s_3806_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3820_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v_val_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v_val_3814_ = lean_ctor_get(v_info_3804_, 0);
lean_inc(v_val_3814_);
lean_dec_ref_known(v_info_3804_, 1);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_val_3814_);
lean_ctor_set(v___x_3815_, 1, v_trees_3810_);
v___x_3816_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3805_, v___x_3815_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 2, v___x_3816_);
v___x_3818_ = v___x_3812_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_assignment_3808_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_lazyAssignment_3809_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v___x_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3819_, sizeof(void*)*3, v_enabled_3807_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
else
{
uint8_t v_enabled_3821_; lean_object* v_assignment_3822_; lean_object* v_lazyAssignment_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3839_; 
v_enabled_3821_ = lean_ctor_get_uint8(v_s_3806_, sizeof(void*)*3);
v_assignment_3822_ = lean_ctor_get(v_s_3806_, 0);
v_lazyAssignment_3823_ = lean_ctor_get(v_s_3806_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_s_3806_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_s_3806_, 2);
lean_dec(v_unused_3840_);
v___x_3825_ = v_s_3806_;
v_isShared_3826_ = v_isSharedCheck_3839_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_lazyAssignment_3823_);
lean_inc(v_assignment_3822_);
lean_dec(v_s_3806_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3839_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_val_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3838_; 
v_val_3827_ = lean_ctor_get(v_info_3804_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_info_3804_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3829_ = v_info_3804_;
v_isShared_3830_ = v_isSharedCheck_3838_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_val_3827_);
lean_dec(v_info_3804_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3838_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 2);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_val_3827_);
v___x_3832_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3833_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3805_, v___x_3832_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 2, v___x_3833_);
v___x_3835_ = v___x_3825_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_assignment_3822_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_lazyAssignment_3823_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v___x_3833_);
lean_ctor_set_uint8(v_reuseFailAlloc_3836_, sizeof(void*)*3, v_enabled_3821_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3841_, lean_object* v_modifyInfoState_3842_, lean_object* v_info_3843_){
_start:
{
lean_object* v___f_3844_; lean_object* v___x_3845_; 
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3844_, 0, v_info_3843_);
lean_closure_set(v___f_3844_, 1, v_treesSaved_3841_);
v___x_3845_ = lean_apply_1(v_modifyInfoState_3842_, v___f_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3846_, lean_object* v_info_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_apply_1(v___f_3846_, v_info_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3849_, lean_object* v_toBind_3850_, lean_object* v___f_3851_, lean_object* v_____do__lift_3852_){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_____do__lift_3852_);
v___x_3854_ = lean_apply_2(v_toPure_3849_, lean_box(0), v___x_3853_);
v___x_3855_ = lean_apply_4(v_toBind_3850_, lean_box(0), lean_box(0), v___x_3854_, v___f_3851_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3856_, lean_object* v_mkInfoOnError_3857_, lean_object* v___f_3858_, lean_object* v_mkInfo_3859_, lean_object* v___f_3860_, lean_object* v_a_x3f_3861_){
_start:
{
if (lean_obj_tag(v_a_x3f_3861_) == 0)
{
lean_object* v___x_3862_; 
lean_dec(v___f_3860_);
lean_dec(v_mkInfo_3859_);
v___x_3862_ = lean_apply_4(v_toBind_3856_, lean_box(0), lean_box(0), v_mkInfoOnError_3857_, v___f_3858_);
return v___x_3862_;
}
else
{
lean_object* v_val_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec(v___f_3858_);
lean_dec(v_mkInfoOnError_3857_);
v_val_3863_ = lean_ctor_get(v_a_x3f_3861_, 0);
lean_inc(v_val_3863_);
lean_dec_ref_known(v_a_x3f_3861_, 1);
v___x_3864_ = lean_apply_1(v_mkInfo_3859_, v_val_3863_);
v___x_3865_ = lean_apply_4(v_toBind_3856_, lean_box(0), lean_box(0), v___x_3864_, v___f_3860_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3866_, lean_object* v_modifyInfoState_3867_, lean_object* v_toBind_3868_, lean_object* v_mkInfoOnError_3869_, lean_object* v_mkInfo_3870_, lean_object* v_inst_3871_, lean_object* v_x_3872_, lean_object* v___f_3873_, lean_object* v_treesSaved_3874_){
_start:
{
lean_object* v_toFunctor_3875_; lean_object* v_toPure_3876_; lean_object* v_map_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___f_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v_toFunctor_3875_ = lean_ctor_get(v_toApplicative_3866_, 0);
lean_inc_ref(v_toFunctor_3875_);
v_toPure_3876_ = lean_ctor_get(v_toApplicative_3866_, 1);
lean_inc(v_toPure_3876_);
lean_dec_ref(v_toApplicative_3866_);
v_map_3877_ = lean_ctor_get(v_toFunctor_3875_, 0);
lean_inc(v_map_3877_);
lean_dec_ref(v_toFunctor_3875_);
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3878_, 0, v_treesSaved_3874_);
lean_closure_set(v___f_3878_, 1, v_modifyInfoState_3867_);
v___f_3879_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3879_, 0, v___f_3878_);
lean_inc_ref(v___f_3879_);
lean_inc(v_toBind_3868_);
v___f_3880_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3880_, 0, v_toPure_3876_);
lean_closure_set(v___f_3880_, 1, v_toBind_3868_);
lean_closure_set(v___f_3880_, 2, v___f_3879_);
v___f_3881_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3881_, 0, v_toBind_3868_);
lean_closure_set(v___f_3881_, 1, v_mkInfoOnError_3869_);
lean_closure_set(v___f_3881_, 2, v___f_3880_);
lean_closure_set(v___f_3881_, 3, v_mkInfo_3870_);
lean_closure_set(v___f_3881_, 4, v___f_3879_);
v___x_3882_ = lean_apply_4(v_inst_3871_, lean_box(0), lean_box(0), v_x_3872_, v___f_3881_);
v___x_3883_ = lean_apply_4(v_map_3877_, lean_box(0), lean_box(0), v___f_3873_, v___x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3884_, lean_object* v_inst_3885_, lean_object* v_inst_3886_, lean_object* v_toBind_3887_, lean_object* v___f_3888_, lean_object* v_____do__lift_3889_){
_start:
{
uint8_t v_enabled_3890_; 
v_enabled_3890_ = lean_ctor_get_uint8(v_____do__lift_3889_, sizeof(void*)*3);
if (v_enabled_3890_ == 0)
{
lean_dec(v___f_3888_);
lean_dec(v_toBind_3887_);
lean_dec_ref(v_inst_3886_);
lean_dec_ref(v_inst_3885_);
lean_inc(v_x_3884_);
return v_x_3884_;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3885_, v_inst_3886_);
v___x_3892_ = lean_apply_4(v_toBind_3887_, lean_box(0), lean_box(0), v___x_3891_, v___f_3888_);
return v___x_3892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3893_, lean_object* v_inst_3894_, lean_object* v_inst_3895_, lean_object* v_toBind_3896_, lean_object* v___f_3897_, lean_object* v_____do__lift_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3893_, v_inst_3894_, v_inst_3895_, v_toBind_3896_, v___f_3897_, v_____do__lift_3898_);
lean_dec_ref(v_____do__lift_3898_);
lean_dec(v_x_3893_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3901_, lean_object* v_inst_3902_, lean_object* v_inst_3903_, lean_object* v_x_3904_, lean_object* v_mkInfo_3905_, lean_object* v_mkInfoOnError_3906_){
_start:
{
lean_object* v_toApplicative_3907_; lean_object* v_toBind_3908_; lean_object* v_getInfoState_3909_; lean_object* v_modifyInfoState_3910_; lean_object* v___f_3911_; lean_object* v___f_3912_; lean_object* v___f_3913_; lean_object* v___x_3914_; 
v_toApplicative_3907_ = lean_ctor_get(v_inst_3901_, 0);
v_toBind_3908_ = lean_ctor_get(v_inst_3901_, 1);
lean_inc_n(v_toBind_3908_, 3);
v_getInfoState_3909_ = lean_ctor_get(v_inst_3902_, 0);
lean_inc(v_getInfoState_3909_);
v_modifyInfoState_3910_ = lean_ctor_get(v_inst_3902_, 1);
v___f_3911_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3904_);
lean_inc(v_modifyInfoState_3910_);
lean_inc_ref(v_toApplicative_3907_);
v___f_3912_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3912_, 0, v_toApplicative_3907_);
lean_closure_set(v___f_3912_, 1, v_modifyInfoState_3910_);
lean_closure_set(v___f_3912_, 2, v_toBind_3908_);
lean_closure_set(v___f_3912_, 3, v_mkInfoOnError_3906_);
lean_closure_set(v___f_3912_, 4, v_mkInfo_3905_);
lean_closure_set(v___f_3912_, 5, v_inst_3903_);
lean_closure_set(v___f_3912_, 6, v_x_3904_);
lean_closure_set(v___f_3912_, 7, v___f_3911_);
v___f_3913_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3913_, 0, v_x_3904_);
lean_closure_set(v___f_3913_, 1, v_inst_3901_);
lean_closure_set(v___f_3913_, 2, v_inst_3902_);
lean_closure_set(v___f_3913_, 3, v_toBind_3908_);
lean_closure_set(v___f_3913_, 4, v___f_3912_);
v___x_3914_ = lean_apply_4(v_toBind_3908_, lean_box(0), lean_box(0), v_getInfoState_3909_, v___f_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3915_, lean_object* v_inst_3916_, lean_object* v_inst_3917_, lean_object* v_00_u03b1_3918_, lean_object* v_inst_3919_, lean_object* v_x_3920_, lean_object* v_mkInfo_3921_, lean_object* v_mkInfoOnError_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3916_, v_inst_3917_, v_inst_3919_, v_x_3920_, v_mkInfo_3921_, v_mkInfoOnError_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3924_, lean_object* v_tree_3925_, lean_object* v_s_3926_){
_start:
{
uint8_t v_enabled_3927_; lean_object* v_assignment_3928_; lean_object* v_lazyAssignment_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3937_; 
v_enabled_3927_ = lean_ctor_get_uint8(v_s_3926_, sizeof(void*)*3);
v_assignment_3928_ = lean_ctor_get(v_s_3926_, 0);
v_lazyAssignment_3929_ = lean_ctor_get(v_s_3926_, 1);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_s_3926_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_s_3926_, 2);
lean_dec(v_unused_3938_);
v___x_3931_ = v_s_3926_;
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_lazyAssignment_3929_);
lean_inc(v_assignment_3928_);
lean_dec(v_s_3926_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3933_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3924_, v_tree_3925_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 2, v___x_3933_);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_assignment_3928_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_lazyAssignment_3929_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v___x_3933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3936_, sizeof(void*)*3, v_enabled_3927_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3939_, lean_object* v_modifyInfoState_3940_, lean_object* v_tree_3941_){
_start:
{
lean_object* v___f_3942_; lean_object* v___x_3943_; 
v___f_3942_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3942_, 0, v_treesSaved_3939_);
lean_closure_set(v___f_3942_, 1, v_tree_3941_);
v___x_3943_ = lean_apply_1(v_modifyInfoState_3940_, v___f_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3944_, lean_object* v_toBind_3945_, lean_object* v___f_3946_, lean_object* v_st_3947_){
_start:
{
lean_object* v_trees_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_trees_3948_ = lean_ctor_get(v_st_3947_, 2);
lean_inc_ref(v_trees_3948_);
lean_dec_ref(v_st_3947_);
v___x_3949_ = lean_apply_1(v_mkInfoTree_3944_, v_trees_3948_);
v___x_3950_ = lean_apply_4(v_toBind_3945_, lean_box(0), lean_box(0), v___x_3949_, v___f_3946_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3951_, lean_object* v_getInfoState_3952_, lean_object* v___f_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_apply_4(v_toBind_3951_, lean_box(0), lean_box(0), v_getInfoState_3952_, v___f_3953_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3956_, lean_object* v_getInfoState_3957_, lean_object* v___f_3958_, lean_object* v_x_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3956_, v_getInfoState_3957_, v___f_3958_, v_x_3959_);
lean_dec(v_x_3959_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3961_, lean_object* v_modifyInfoState_3962_, lean_object* v_mkInfoTree_3963_, lean_object* v_toBind_3964_, lean_object* v_getInfoState_3965_, lean_object* v_inst_3966_, lean_object* v_x_3967_, lean_object* v___f_3968_, lean_object* v_treesSaved_3969_){
_start:
{
lean_object* v_toFunctor_3970_; lean_object* v_map_3971_; lean_object* v___f_3972_; lean_object* v___f_3973_; lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_toFunctor_3970_ = lean_ctor_get(v_toApplicative_3961_, 0);
lean_inc_ref(v_toFunctor_3970_);
lean_dec_ref(v_toApplicative_3961_);
v_map_3971_ = lean_ctor_get(v_toFunctor_3970_, 0);
lean_inc(v_map_3971_);
lean_dec_ref(v_toFunctor_3970_);
v___f_3972_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3972_, 0, v_treesSaved_3969_);
lean_closure_set(v___f_3972_, 1, v_modifyInfoState_3962_);
lean_inc(v_toBind_3964_);
v___f_3973_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3973_, 0, v_mkInfoTree_3963_);
lean_closure_set(v___f_3973_, 1, v_toBind_3964_);
lean_closure_set(v___f_3973_, 2, v___f_3972_);
v___f_3974_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3974_, 0, v_toBind_3964_);
lean_closure_set(v___f_3974_, 1, v_getInfoState_3965_);
lean_closure_set(v___f_3974_, 2, v___f_3973_);
v___x_3975_ = lean_apply_4(v_inst_3966_, lean_box(0), lean_box(0), v_x_3967_, v___f_3974_);
v___x_3976_ = lean_apply_4(v_map_3971_, lean_box(0), lean_box(0), v___f_3968_, v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3977_, lean_object* v_inst_3978_, lean_object* v_inst_3979_, lean_object* v_x_3980_, lean_object* v_mkInfoTree_3981_){
_start:
{
lean_object* v_toApplicative_3982_; lean_object* v_toBind_3983_; lean_object* v_getInfoState_3984_; lean_object* v_modifyInfoState_3985_; lean_object* v___f_3986_; lean_object* v___f_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; 
v_toApplicative_3982_ = lean_ctor_get(v_inst_3977_, 0);
v_toBind_3983_ = lean_ctor_get(v_inst_3977_, 1);
lean_inc_n(v_toBind_3983_, 3);
v_getInfoState_3984_ = lean_ctor_get(v_inst_3978_, 0);
lean_inc_n(v_getInfoState_3984_, 2);
v_modifyInfoState_3985_ = lean_ctor_get(v_inst_3978_, 1);
v___f_3986_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3980_);
lean_inc(v_modifyInfoState_3985_);
lean_inc_ref(v_toApplicative_3982_);
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3987_, 0, v_toApplicative_3982_);
lean_closure_set(v___f_3987_, 1, v_modifyInfoState_3985_);
lean_closure_set(v___f_3987_, 2, v_mkInfoTree_3981_);
lean_closure_set(v___f_3987_, 3, v_toBind_3983_);
lean_closure_set(v___f_3987_, 4, v_getInfoState_3984_);
lean_closure_set(v___f_3987_, 5, v_inst_3979_);
lean_closure_set(v___f_3987_, 6, v_x_3980_);
lean_closure_set(v___f_3987_, 7, v___f_3986_);
v___f_3988_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3988_, 0, v_x_3980_);
lean_closure_set(v___f_3988_, 1, v_inst_3977_);
lean_closure_set(v___f_3988_, 2, v_inst_3978_);
lean_closure_set(v___f_3988_, 3, v_toBind_3983_);
lean_closure_set(v___f_3988_, 4, v___f_3987_);
v___x_3989_ = lean_apply_4(v_toBind_3983_, lean_box(0), lean_box(0), v_getInfoState_3984_, v___f_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3990_, lean_object* v_inst_3991_, lean_object* v_inst_3992_, lean_object* v_00_u03b1_3993_, lean_object* v_inst_3994_, lean_object* v_x_3995_, lean_object* v_mkInfoTree_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3991_, v_inst_3992_, v_inst_3994_, v_x_3995_, v_mkInfoTree_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3998_, lean_object* v_toPure_3999_, lean_object* v_____do__lift_4000_){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v_____do__lift_4000_);
lean_ctor_set(v___x_4001_, 1, v_trees_3998_);
v___x_4002_ = lean_apply_2(v_toPure_3999_, lean_box(0), v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_4003_, lean_object* v_toBind_4004_, lean_object* v_mkInfo_4005_, lean_object* v_trees_4006_){
_start:
{
lean_object* v___f_4007_; lean_object* v___x_4008_; 
v___f_4007_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4007_, 0, v_trees_4006_);
lean_closure_set(v___f_4007_, 1, v_toPure_4003_);
v___x_4008_ = lean_apply_4(v_toBind_4004_, lean_box(0), lean_box(0), v_mkInfo_4005_, v___f_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_4009_, lean_object* v_inst_4010_, lean_object* v_inst_4011_, lean_object* v_x_4012_, lean_object* v_mkInfo_4013_){
_start:
{
lean_object* v_toApplicative_4014_; lean_object* v_toBind_4015_; lean_object* v_toPure_4016_; lean_object* v___f_4017_; lean_object* v___x_4018_; 
v_toApplicative_4014_ = lean_ctor_get(v_inst_4009_, 0);
v_toBind_4015_ = lean_ctor_get(v_inst_4009_, 1);
v_toPure_4016_ = lean_ctor_get(v_toApplicative_4014_, 1);
lean_inc(v_toBind_4015_);
lean_inc(v_toPure_4016_);
v___f_4017_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4017_, 0, v_toPure_4016_);
lean_closure_set(v___f_4017_, 1, v_toBind_4015_);
lean_closure_set(v___f_4017_, 2, v_mkInfo_4013_);
v___x_4018_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4009_, v_inst_4010_, v_inst_4011_, v_x_4012_, v___f_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_4019_, lean_object* v_inst_4020_, lean_object* v_inst_4021_, lean_object* v_00_u03b1_4022_, lean_object* v_inst_4023_, lean_object* v_x_4024_, lean_object* v_mkInfo_4025_){
_start:
{
lean_object* v_toApplicative_4026_; lean_object* v_toBind_4027_; lean_object* v_toPure_4028_; lean_object* v___f_4029_; lean_object* v___x_4030_; 
v_toApplicative_4026_ = lean_ctor_get(v_inst_4020_, 0);
v_toBind_4027_ = lean_ctor_get(v_inst_4020_, 1);
v_toPure_4028_ = lean_ctor_get(v_toApplicative_4026_, 1);
lean_inc(v_toBind_4027_);
lean_inc(v_toPure_4028_);
v___f_4029_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4029_, 0, v_toPure_4028_);
lean_closure_set(v___f_4029_, 1, v_toBind_4027_);
lean_closure_set(v___f_4029_, 2, v_mkInfo_4025_);
v___x_4030_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4020_, v_inst_4021_, v_inst_4023_, v_x_4024_, v___f_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_4031_, lean_object* v_trees_4032_, lean_object* v_s_4033_){
_start:
{
uint8_t v_enabled_4034_; lean_object* v_assignment_4035_; lean_object* v_lazyAssignment_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4044_; 
v_enabled_4034_ = lean_ctor_get_uint8(v_s_4033_, sizeof(void*)*3);
v_assignment_4035_ = lean_ctor_get(v_s_4033_, 0);
v_lazyAssignment_4036_ = lean_ctor_get(v_s_4033_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_s_4033_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v_s_4033_, 2);
lean_dec(v_unused_4045_);
v___x_4038_ = v_s_4033_;
v_isShared_4039_ = v_isSharedCheck_4044_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_lazyAssignment_4036_);
lean_inc(v_assignment_4035_);
lean_dec(v_s_4033_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4044_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
v___x_4040_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_4031_, v_trees_4032_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 2, v___x_4040_);
v___x_4042_ = v___x_4038_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_assignment_4035_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_lazyAssignment_4036_);
lean_ctor_set(v_reuseFailAlloc_4043_, 2, v___x_4040_);
lean_ctor_set_uint8(v_reuseFailAlloc_4043_, sizeof(void*)*3, v_enabled_4034_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_4046_, lean_object* v_trees_4047_, lean_object* v_s_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_4046_, v_trees_4047_, v_s_4048_);
lean_dec_ref(v_trees_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_4050_, lean_object* v_modifyInfoState_4051_, lean_object* v_trees_4052_){
_start:
{
lean_object* v___f_4053_; lean_object* v___x_4054_; 
v___f_4053_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4053_, 0, v_treesSaved_4050_);
lean_closure_set(v___f_4053_, 1, v_trees_4052_);
v___x_4054_ = lean_apply_1(v_modifyInfoState_4051_, v___f_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_4055_, lean_object* v_tree_4056_, lean_object* v_____do__lift_4057_){
_start:
{
if (lean_obj_tag(v_____do__lift_4057_) == 0)
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_apply_2(v_toPure_4055_, lean_box(0), v_tree_4056_);
return v___x_4058_;
}
else
{
lean_object* v_val_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_val_4059_ = lean_ctor_get(v_____do__lift_4057_, 0);
lean_inc(v_val_4059_);
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_val_4059_);
lean_ctor_set(v___x_4060_, 1, v_tree_4056_);
v___x_4061_ = lean_apply_2(v_toPure_4055_, lean_box(0), v___x_4060_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_4062_, lean_object* v_tree_4063_, lean_object* v_____do__lift_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_4062_, v_tree_4063_, v_____do__lift_4064_);
lean_dec(v_____do__lift_4064_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4066_, lean_object* v_toPure_4067_, lean_object* v_toBind_4068_, lean_object* v_ctx_x3f_4069_, lean_object* v_tree_4070_){
_start:
{
lean_object* v_tree_4071_; lean_object* v___f_4072_; lean_object* v___x_4073_; 
v_tree_4071_ = l_Lean_Elab_InfoTree_substitute(v_tree_4070_, v_assignment_4066_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4072_, 0, v_toPure_4067_);
lean_closure_set(v___f_4072_, 1, v_tree_4071_);
v___x_4073_ = lean_apply_4(v_toBind_4068_, lean_box(0), lean_box(0), v_ctx_x3f_4069_, v___f_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_4074_, lean_object* v_toPure_4075_, lean_object* v_toBind_4076_, lean_object* v_ctx_x3f_4077_, lean_object* v_tree_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_4074_, v_toPure_4075_, v_toBind_4076_, v_ctx_x3f_4077_, v_tree_4078_);
lean_dec_ref(v_assignment_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4080_, lean_object* v_toBind_4081_, lean_object* v_ctx_x3f_4082_, lean_object* v_inst_4083_, lean_object* v___f_4084_, lean_object* v_st_4085_){
_start:
{
lean_object* v_assignment_4086_; lean_object* v_trees_4087_; lean_object* v___f_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_assignment_4086_ = lean_ctor_get(v_st_4085_, 0);
lean_inc_ref(v_assignment_4086_);
v_trees_4087_ = lean_ctor_get(v_st_4085_, 2);
lean_inc_ref(v_trees_4087_);
lean_dec_ref(v_st_4085_);
lean_inc(v_toBind_4081_);
v___f_4088_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4088_, 0, v_assignment_4086_);
lean_closure_set(v___f_4088_, 1, v_toPure_4080_);
lean_closure_set(v___f_4088_, 2, v_toBind_4081_);
lean_closure_set(v___f_4088_, 3, v_ctx_x3f_4082_);
v___x_4089_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4083_, v___f_4088_, v_trees_4087_);
v___x_4090_ = lean_apply_4(v_toBind_4081_, lean_box(0), lean_box(0), v___x_4089_, v___f_4084_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4091_, lean_object* v_modifyInfoState_4092_, lean_object* v_toBind_4093_, lean_object* v_ctx_x3f_4094_, lean_object* v_inst_4095_, lean_object* v_getInfoState_4096_, lean_object* v_inst_4097_, lean_object* v_x_4098_, lean_object* v___f_4099_, lean_object* v_treesSaved_4100_){
_start:
{
lean_object* v_toFunctor_4101_; lean_object* v_toPure_4102_; lean_object* v_map_4103_; lean_object* v___f_4104_; lean_object* v___f_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_toFunctor_4101_ = lean_ctor_get(v_toApplicative_4091_, 0);
lean_inc_ref(v_toFunctor_4101_);
v_toPure_4102_ = lean_ctor_get(v_toApplicative_4091_, 1);
lean_inc(v_toPure_4102_);
lean_dec_ref(v_toApplicative_4091_);
v_map_4103_ = lean_ctor_get(v_toFunctor_4101_, 0);
lean_inc(v_map_4103_);
lean_dec_ref(v_toFunctor_4101_);
v___f_4104_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4104_, 0, v_treesSaved_4100_);
lean_closure_set(v___f_4104_, 1, v_modifyInfoState_4092_);
lean_inc(v_toBind_4093_);
v___f_4105_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4105_, 0, v_toPure_4102_);
lean_closure_set(v___f_4105_, 1, v_toBind_4093_);
lean_closure_set(v___f_4105_, 2, v_ctx_x3f_4094_);
lean_closure_set(v___f_4105_, 3, v_inst_4095_);
lean_closure_set(v___f_4105_, 4, v___f_4104_);
v___f_4106_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4106_, 0, v_toBind_4093_);
lean_closure_set(v___f_4106_, 1, v_getInfoState_4096_);
lean_closure_set(v___f_4106_, 2, v___f_4105_);
v___x_4107_ = lean_apply_4(v_inst_4097_, lean_box(0), lean_box(0), v_x_4098_, v___f_4106_);
v___x_4108_ = lean_apply_4(v_map_4103_, lean_box(0), lean_box(0), v___f_4099_, v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4109_, lean_object* v_inst_4110_, lean_object* v_inst_4111_, lean_object* v_x_4112_, lean_object* v_ctx_x3f_4113_){
_start:
{
lean_object* v_toApplicative_4114_; lean_object* v_toBind_4115_; lean_object* v_getInfoState_4116_; lean_object* v_modifyInfoState_4117_; lean_object* v___f_4118_; lean_object* v___f_4119_; lean_object* v___f_4120_; lean_object* v___x_4121_; 
v_toApplicative_4114_ = lean_ctor_get(v_inst_4109_, 0);
v_toBind_4115_ = lean_ctor_get(v_inst_4109_, 1);
lean_inc_n(v_toBind_4115_, 3);
v_getInfoState_4116_ = lean_ctor_get(v_inst_4110_, 0);
lean_inc_n(v_getInfoState_4116_, 2);
v_modifyInfoState_4117_ = lean_ctor_get(v_inst_4110_, 1);
v___f_4118_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4112_);
lean_inc_ref(v_inst_4109_);
lean_inc(v_modifyInfoState_4117_);
lean_inc_ref(v_toApplicative_4114_);
v___f_4119_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4119_, 0, v_toApplicative_4114_);
lean_closure_set(v___f_4119_, 1, v_modifyInfoState_4117_);
lean_closure_set(v___f_4119_, 2, v_toBind_4115_);
lean_closure_set(v___f_4119_, 3, v_ctx_x3f_4113_);
lean_closure_set(v___f_4119_, 4, v_inst_4109_);
lean_closure_set(v___f_4119_, 5, v_getInfoState_4116_);
lean_closure_set(v___f_4119_, 6, v_inst_4111_);
lean_closure_set(v___f_4119_, 7, v_x_4112_);
lean_closure_set(v___f_4119_, 8, v___f_4118_);
v___f_4120_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4120_, 0, v_x_4112_);
lean_closure_set(v___f_4120_, 1, v_inst_4109_);
lean_closure_set(v___f_4120_, 2, v_inst_4110_);
lean_closure_set(v___f_4120_, 3, v_toBind_4115_);
lean_closure_set(v___f_4120_, 4, v___f_4119_);
v___x_4121_ = lean_apply_4(v_toBind_4115_, lean_box(0), lean_box(0), v_getInfoState_4116_, v___f_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4122_, lean_object* v_inst_4123_, lean_object* v_inst_4124_, lean_object* v_00_u03b1_4125_, lean_object* v_inst_4126_, lean_object* v_x_4127_, lean_object* v_ctx_x3f_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4123_, v_inst_4124_, v_inst_4126_, v_x_4127_, v_ctx_x3f_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4130_, lean_object* v_____do__lift_4131_){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_____do__lift_4131_);
v___x_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
v___x_4134_ = lean_apply_2(v_toPure_4130_, lean_box(0), v___x_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4135_, lean_object* v_inst_4136_, lean_object* v_inst_4137_, lean_object* v_inst_4138_, lean_object* v_inst_4139_, lean_object* v_inst_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_inst_4143_, lean_object* v_x_4144_){
_start:
{
lean_object* v_toApplicative_4145_; lean_object* v_toBind_4146_; lean_object* v_toPure_4147_; lean_object* v___x_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_toApplicative_4145_ = lean_ctor_get(v_inst_4135_, 0);
v_toBind_4146_ = lean_ctor_get(v_inst_4135_, 1);
v_toPure_4147_ = lean_ctor_get(v_toApplicative_4145_, 1);
lean_inc_ref(v_inst_4135_);
v___x_4148_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4135_, v_inst_4139_, v_inst_4141_, v_inst_4140_, v_inst_4142_, v_inst_4137_, v_inst_4143_);
lean_inc(v_toPure_4147_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4149_, 0, v_toPure_4147_);
lean_inc(v_toBind_4146_);
v___x_4150_ = lean_apply_4(v_toBind_4146_, lean_box(0), lean_box(0), v___x_4148_, v___f_4149_);
v___x_4151_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4135_, v_inst_4136_, v_inst_4138_, v_x_4144_, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4152_, lean_object* v_inst_4153_, lean_object* v_inst_4154_, lean_object* v_00_u03b1_4155_, lean_object* v_inst_4156_, lean_object* v_inst_4157_, lean_object* v_inst_4158_, lean_object* v_inst_4159_, lean_object* v_inst_4160_, lean_object* v_inst_4161_, lean_object* v_inst_4162_, lean_object* v_x_4163_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4153_, v_inst_4154_, v_inst_4156_, v_inst_4157_, v_inst_4158_, v_inst_4159_, v_inst_4160_, v_inst_4161_, v_inst_4162_, v_x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4165_, lean_object* v_____x_4166_){
_start:
{
if (lean_obj_tag(v_____x_4166_) == 1)
{
lean_object* v_val_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4176_; 
v_val_4167_ = lean_ctor_get(v_____x_4166_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_____x_4166_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4169_ = v_____x_4166_;
v_isShared_4170_ = v_isSharedCheck_4176_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_val_4167_);
lean_dec(v_____x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4176_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4171_, 0, v_val_4167_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_apply_2(v_toPure_4165_, lean_box(0), v___x_4173_);
return v___x_4174_;
}
}
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec(v_____x_4166_);
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_apply_2(v_toPure_4165_, lean_box(0), v___x_4177_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4179_, lean_object* v_inst_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_x_4183_){
_start:
{
lean_object* v_toApplicative_4184_; lean_object* v_toBind_4185_; lean_object* v_toPure_4186_; lean_object* v___f_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_toApplicative_4184_ = lean_ctor_get(v_inst_4179_, 0);
v_toBind_4185_ = lean_ctor_get(v_inst_4179_, 1);
v_toPure_4186_ = lean_ctor_get(v_toApplicative_4184_, 1);
lean_inc(v_toPure_4186_);
v___f_4187_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4187_, 0, v_toPure_4186_);
lean_inc(v_toBind_4185_);
v___x_4188_ = lean_apply_4(v_toBind_4185_, lean_box(0), lean_box(0), v_inst_4182_, v___f_4187_);
v___x_4189_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4179_, v_inst_4180_, v_inst_4181_, v_x_4183_, v___x_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4190_, lean_object* v_inst_4191_, lean_object* v_inst_4192_, lean_object* v_00_u03b1_4193_, lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_x_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4191_, v_inst_4192_, v_inst_4194_, v_inst_4195_, v_x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4198_, lean_object* v_autoImplicits_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_autoImplicits_4199_);
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
v___x_4202_ = lean_apply_2(v_toPure_4198_, lean_box(0), v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4203_, lean_object* v_inst_4204_, lean_object* v_inst_4205_, lean_object* v_inst_4206_, lean_object* v_x_4207_){
_start:
{
lean_object* v_toApplicative_4208_; lean_object* v_toBind_4209_; lean_object* v_toPure_4210_; lean_object* v___f_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_toApplicative_4208_ = lean_ctor_get(v_inst_4203_, 0);
v_toBind_4209_ = lean_ctor_get(v_inst_4203_, 1);
v_toPure_4210_ = lean_ctor_get(v_toApplicative_4208_, 1);
lean_inc(v_toPure_4210_);
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4211_, 0, v_toPure_4210_);
lean_inc(v_toBind_4209_);
v___x_4212_ = lean_apply_4(v_toBind_4209_, lean_box(0), lean_box(0), v_inst_4206_, v___f_4211_);
v___x_4213_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4203_, v_inst_4204_, v_inst_4205_, v_x_4207_, v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4214_, lean_object* v_inst_4215_, lean_object* v_inst_4216_, lean_object* v_00_u03b1_4217_, lean_object* v_inst_4218_, lean_object* v_inst_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4215_, v_inst_4216_, v_inst_4218_, v_inst_4219_, v_x_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v_mvarId_4224_, lean_object* v_toPure_4225_, lean_object* v_____do__lift_4226_){
_start:
{
lean_object* v_assignment_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_assignment_4227_ = lean_ctor_get(v_____do__lift_4226_, 0);
v___x_4228_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4222_, v___x_4223_, v_assignment_4227_, v_mvarId_4224_);
v___x_4229_ = lean_apply_2(v_toPure_4225_, lean_box(0), v___x_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v_mvarId_4232_, lean_object* v_toPure_4233_, lean_object* v_____do__lift_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_4230_, v___x_4231_, v_mvarId_4232_, v_toPure_4233_, v_____do__lift_4234_);
lean_dec_ref(v_____do__lift_4234_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4238_, lean_object* v_inst_4239_, lean_object* v_mvarId_4240_){
_start:
{
lean_object* v_toApplicative_4241_; lean_object* v_toBind_4242_; lean_object* v_getInfoState_4243_; lean_object* v_toPure_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___f_4247_; lean_object* v___x_4248_; 
v_toApplicative_4241_ = lean_ctor_get(v_inst_4238_, 0);
lean_inc_ref(v_toApplicative_4241_);
v_toBind_4242_ = lean_ctor_get(v_inst_4238_, 1);
lean_inc(v_toBind_4242_);
lean_dec_ref(v_inst_4238_);
v_getInfoState_4243_ = lean_ctor_get(v_inst_4239_, 0);
lean_inc(v_getInfoState_4243_);
lean_dec_ref(v_inst_4239_);
v_toPure_4244_ = lean_ctor_get(v_toApplicative_4241_, 1);
lean_inc(v_toPure_4244_);
lean_dec_ref(v_toApplicative_4241_);
v___x_4245_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4246_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4247_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4247_, 0, v___x_4245_);
lean_closure_set(v___f_4247_, 1, v___x_4246_);
lean_closure_set(v___f_4247_, 2, v_mvarId_4240_);
lean_closure_set(v___f_4247_, 3, v_toPure_4244_);
v___x_4248_ = lean_apply_4(v_toBind_4242_, lean_box(0), lean_box(0), v_getInfoState_4243_, v___f_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4249_, lean_object* v_inst_4250_, lean_object* v_inst_4251_, lean_object* v_mvarId_4252_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4250_, v_inst_4251_, v_mvarId_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4254_, lean_object* v_infoTree_4255_, lean_object* v_s_4256_){
_start:
{
uint8_t v_enabled_4257_; lean_object* v_assignment_4258_; lean_object* v_lazyAssignment_4259_; lean_object* v_trees_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4270_; 
v_enabled_4257_ = lean_ctor_get_uint8(v_s_4256_, sizeof(void*)*3);
v_assignment_4258_ = lean_ctor_get(v_s_4256_, 0);
v_lazyAssignment_4259_ = lean_ctor_get(v_s_4256_, 1);
v_trees_4260_ = lean_ctor_get(v_s_4256_, 2);
v_isSharedCheck_4270_ = !lean_is_exclusive(v_s_4256_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4262_ = v_s_4256_;
v_isShared_4263_ = v_isSharedCheck_4270_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_trees_4260_);
lean_inc(v_lazyAssignment_4259_);
lean_inc(v_assignment_4258_);
lean_dec(v_s_4256_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4270_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4264_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4265_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4266_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4264_, v___x_4265_, v_assignment_4258_, v_mvarId_4254_, v_infoTree_4255_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4266_);
v___x_4268_ = v___x_4262_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_lazyAssignment_4259_);
lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_trees_4260_);
lean_ctor_set_uint8(v_reuseFailAlloc_4269_, sizeof(void*)*3, v_enabled_4257_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4273_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4274_ = lean_unsigned_to_nat(2u);
v___x_4275_ = lean_unsigned_to_nat(491u);
v___x_4276_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4277_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4278_ = l_mkPanicMessageWithDecl(v___x_4277_, v___x_4276_, v___x_4275_, v___x_4274_, v___x_4273_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4279_, lean_object* v___f_4280_, lean_object* v_inst_4281_, lean_object* v_____do__lift_4282_){
_start:
{
if (lean_obj_tag(v_____do__lift_4282_) == 0)
{
lean_object* v_modifyInfoState_4283_; lean_object* v___x_4284_; 
lean_dec_ref(v_inst_4281_);
v_modifyInfoState_4283_ = lean_ctor_get(v_inst_4279_, 1);
lean_inc(v_modifyInfoState_4283_);
lean_dec_ref(v_inst_4279_);
v___x_4284_ = lean_apply_1(v_modifyInfoState_4283_, v___f_4280_);
return v___x_4284_;
}
else
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
lean_dec_ref(v___f_4280_);
lean_dec_ref(v_inst_4279_);
v___x_4285_ = lean_box(0);
v___x_4286_ = l_instInhabitedOfMonad___redArg(v_inst_4281_, v___x_4285_);
v___x_4287_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4288_ = l_panic___redArg(v___x_4286_, v___x_4287_);
lean_dec(v___x_4286_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4289_, lean_object* v___f_4290_, lean_object* v_inst_4291_, lean_object* v_____do__lift_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4289_, v___f_4290_, v_inst_4291_, v_____do__lift_4292_);
lean_dec(v_____do__lift_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4294_, lean_object* v_inst_4295_, lean_object* v_mvarId_4296_, lean_object* v_infoTree_4297_){
_start:
{
lean_object* v_toBind_4298_; lean_object* v___f_4299_; lean_object* v___f_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_toBind_4298_ = lean_ctor_get(v_inst_4294_, 1);
lean_inc(v_toBind_4298_);
lean_inc(v_mvarId_4296_);
v___f_4299_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4299_, 0, v_mvarId_4296_);
lean_closure_set(v___f_4299_, 1, v_infoTree_4297_);
lean_inc_ref(v_inst_4294_);
lean_inc_ref(v_inst_4295_);
v___f_4300_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4300_, 0, v_inst_4295_);
lean_closure_set(v___f_4300_, 1, v___f_4299_);
lean_closure_set(v___f_4300_, 2, v_inst_4294_);
v___x_4301_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4294_, v_inst_4295_, v_mvarId_4296_);
v___x_4302_ = lean_apply_4(v_toBind_4298_, lean_box(0), lean_box(0), v___x_4301_, v___f_4300_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4303_, lean_object* v_inst_4304_, lean_object* v_inst_4305_, lean_object* v_mvarId_4306_, lean_object* v_infoTree_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4304_, v_inst_4305_, v_mvarId_4306_, v_infoTree_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4309_, lean_object* v_output_4310_, lean_object* v_toPure_4311_, lean_object* v_____do__lift_4312_){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4313_, 0, v_____do__lift_4312_);
lean_ctor_set(v___x_4313_, 1, v_stx_4309_);
lean_ctor_set(v___x_4313_, 2, v_output_4310_);
v___x_4314_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
v___x_4315_ = lean_apply_2(v_toPure_4311_, lean_box(0), v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4316_, lean_object* v_inst_4317_, lean_object* v_inst_4318_, lean_object* v_inst_4319_, lean_object* v_stx_4320_, lean_object* v_output_4321_, lean_object* v_x_4322_){
_start:
{
lean_object* v_toApplicative_4323_; lean_object* v_toBind_4324_; lean_object* v_toPure_4325_; lean_object* v___f_4326_; lean_object* v_mkInfo_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; 
v_toApplicative_4323_ = lean_ctor_get(v_inst_4317_, 0);
v_toBind_4324_ = lean_ctor_get(v_inst_4317_, 1);
v_toPure_4325_ = lean_ctor_get(v_toApplicative_4323_, 1);
lean_inc_n(v_toPure_4325_, 2);
v___f_4326_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4326_, 0, v_stx_4320_);
lean_closure_set(v___f_4326_, 1, v_output_4321_);
lean_closure_set(v___f_4326_, 2, v_toPure_4325_);
lean_inc_n(v_toBind_4324_, 2);
v_mkInfo_4327_ = lean_apply_4(v_toBind_4324_, lean_box(0), lean_box(0), v_inst_4319_, v___f_4326_);
v___f_4328_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4328_, 0, v_toPure_4325_);
lean_closure_set(v___f_4328_, 1, v_toBind_4324_);
lean_closure_set(v___f_4328_, 2, v_mkInfo_4327_);
v___x_4329_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4317_, v_inst_4318_, v_inst_4316_, v_x_4322_, v___f_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4330_, lean_object* v_00_u03b1_4331_, lean_object* v_inst_4332_, lean_object* v_inst_4333_, lean_object* v_inst_4334_, lean_object* v_inst_4335_, lean_object* v_stx_4336_, lean_object* v_output_4337_, lean_object* v_x_4338_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4332_, v_inst_4333_, v_inst_4334_, v_inst_4335_, v_stx_4336_, v_output_4337_, v_x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4340_, lean_object* v_mvarId_4341_, lean_object* v_s_4342_){
_start:
{
lean_object* v_trees_4343_; uint8_t v_enabled_4344_; lean_object* v_assignment_4345_; lean_object* v_lazyAssignment_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4366_; 
v_trees_4343_ = lean_ctor_get(v_s_4342_, 2);
v_enabled_4344_ = lean_ctor_get_uint8(v_s_4342_, sizeof(void*)*3);
v_assignment_4345_ = lean_ctor_get(v_s_4342_, 0);
v_lazyAssignment_4346_ = lean_ctor_get(v_s_4342_, 1);
v_isSharedCheck_4366_ = !lean_is_exclusive(v_s_4342_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4348_ = v_s_4342_;
v_isShared_4349_ = v_isSharedCheck_4366_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_trees_4343_);
lean_inc(v_lazyAssignment_4346_);
lean_inc(v_assignment_4345_);
lean_dec(v_s_4342_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4366_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v_size_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_size_4350_ = lean_ctor_get(v_trees_4343_, 2);
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = lean_nat_dec_lt(v___x_4351_, v_size_4350_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4354_; 
lean_dec_ref(v_trees_4343_);
lean_dec(v_mvarId_4341_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 2, v_treesSaved_4340_);
v___x_4354_ = v___x_4348_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_assignment_4345_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_lazyAssignment_4346_);
lean_ctor_set(v_reuseFailAlloc_4355_, 2, v_treesSaved_4340_);
lean_ctor_set_uint8(v_reuseFailAlloc_4355_, sizeof(void*)*3, v_enabled_4344_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4364_; 
v___x_4356_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4357_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4358_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4359_ = lean_unsigned_to_nat(1u);
v___x_4360_ = lean_nat_sub(v_size_4350_, v___x_4359_);
v___x_4361_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4358_, v_trees_4343_, v___x_4360_);
lean_dec(v___x_4360_);
lean_dec_ref(v_trees_4343_);
v___x_4362_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4356_, v___x_4357_, v_assignment_4345_, v_mvarId_4341_, v___x_4361_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 2, v_treesSaved_4340_);
lean_ctor_set(v___x_4348_, 0, v___x_4362_);
v___x_4364_ = v___x_4348_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_lazyAssignment_4346_);
lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_treesSaved_4340_);
lean_ctor_set_uint8(v_reuseFailAlloc_4365_, sizeof(void*)*3, v_enabled_4344_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4367_, lean_object* v___f_4368_, lean_object* v_x_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = lean_apply_1(v_modifyInfoState_4367_, v___f_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4371_, lean_object* v___f_4372_, lean_object* v_x_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4371_, v___f_4372_, v_x_4373_);
lean_dec(v_x_4373_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4375_, lean_object* v_mvarId_4376_, lean_object* v_modifyInfoState_4377_, lean_object* v_inst_4378_, lean_object* v_x_4379_, lean_object* v___f_4380_, lean_object* v_treesSaved_4381_){
_start:
{
lean_object* v_toFunctor_4382_; lean_object* v_map_4383_; lean_object* v___f_4384_; lean_object* v___f_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_toFunctor_4382_ = lean_ctor_get(v_toApplicative_4375_, 0);
lean_inc_ref(v_toFunctor_4382_);
lean_dec_ref(v_toApplicative_4375_);
v_map_4383_ = lean_ctor_get(v_toFunctor_4382_, 0);
lean_inc(v_map_4383_);
lean_dec_ref(v_toFunctor_4382_);
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4384_, 0, v_treesSaved_4381_);
lean_closure_set(v___f_4384_, 1, v_mvarId_4376_);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4385_, 0, v_modifyInfoState_4377_);
lean_closure_set(v___f_4385_, 1, v___f_4384_);
v___x_4386_ = lean_apply_4(v_inst_4378_, lean_box(0), lean_box(0), v_x_4379_, v___f_4385_);
v___x_4387_ = lean_apply_4(v_map_4383_, lean_box(0), lean_box(0), v___f_4380_, v___x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4388_, lean_object* v_inst_4389_, lean_object* v_inst_4390_, lean_object* v_mvarId_4391_, lean_object* v_x_4392_){
_start:
{
lean_object* v_toApplicative_4393_; lean_object* v_toBind_4394_; lean_object* v_getInfoState_4395_; lean_object* v_modifyInfoState_4396_; lean_object* v___f_4397_; lean_object* v___f_4398_; lean_object* v___f_4399_; lean_object* v___x_4400_; 
v_toApplicative_4393_ = lean_ctor_get(v_inst_4389_, 0);
v_toBind_4394_ = lean_ctor_get(v_inst_4389_, 1);
lean_inc_n(v_toBind_4394_, 2);
v_getInfoState_4395_ = lean_ctor_get(v_inst_4390_, 0);
lean_inc(v_getInfoState_4395_);
v_modifyInfoState_4396_ = lean_ctor_get(v_inst_4390_, 1);
v___f_4397_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4392_);
lean_inc(v_modifyInfoState_4396_);
lean_inc_ref(v_toApplicative_4393_);
v___f_4398_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4398_, 0, v_toApplicative_4393_);
lean_closure_set(v___f_4398_, 1, v_mvarId_4391_);
lean_closure_set(v___f_4398_, 2, v_modifyInfoState_4396_);
lean_closure_set(v___f_4398_, 3, v_inst_4388_);
lean_closure_set(v___f_4398_, 4, v_x_4392_);
lean_closure_set(v___f_4398_, 5, v___f_4397_);
v___f_4399_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4399_, 0, v_x_4392_);
lean_closure_set(v___f_4399_, 1, v_inst_4389_);
lean_closure_set(v___f_4399_, 2, v_inst_4390_);
lean_closure_set(v___f_4399_, 3, v_toBind_4394_);
lean_closure_set(v___f_4399_, 4, v___f_4398_);
v___x_4400_ = lean_apply_4(v_toBind_4394_, lean_box(0), lean_box(0), v_getInfoState_4395_, v___f_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4401_, lean_object* v_00_u03b1_4402_, lean_object* v_inst_4403_, lean_object* v_inst_4404_, lean_object* v_inst_4405_, lean_object* v_mvarId_4406_, lean_object* v_x_4407_){
_start:
{
lean_object* v_toApplicative_4408_; lean_object* v_toBind_4409_; lean_object* v_getInfoState_4410_; lean_object* v_modifyInfoState_4411_; lean_object* v___f_4412_; lean_object* v___f_4413_; lean_object* v___f_4414_; lean_object* v___x_4415_; 
v_toApplicative_4408_ = lean_ctor_get(v_inst_4404_, 0);
v_toBind_4409_ = lean_ctor_get(v_inst_4404_, 1);
lean_inc_n(v_toBind_4409_, 2);
v_getInfoState_4410_ = lean_ctor_get(v_inst_4405_, 0);
lean_inc(v_getInfoState_4410_);
v_modifyInfoState_4411_ = lean_ctor_get(v_inst_4405_, 1);
v___f_4412_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4407_);
lean_inc(v_modifyInfoState_4411_);
lean_inc_ref(v_toApplicative_4408_);
v___f_4413_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4413_, 0, v_toApplicative_4408_);
lean_closure_set(v___f_4413_, 1, v_mvarId_4406_);
lean_closure_set(v___f_4413_, 2, v_modifyInfoState_4411_);
lean_closure_set(v___f_4413_, 3, v_inst_4403_);
lean_closure_set(v___f_4413_, 4, v_x_4407_);
lean_closure_set(v___f_4413_, 5, v___f_4412_);
v___f_4414_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4414_, 0, v_x_4407_);
lean_closure_set(v___f_4414_, 1, v_inst_4404_);
lean_closure_set(v___f_4414_, 2, v_inst_4405_);
lean_closure_set(v___f_4414_, 3, v_toBind_4409_);
lean_closure_set(v___f_4414_, 4, v___f_4413_);
v___x_4415_ = lean_apply_4(v_toBind_4409_, lean_box(0), lean_box(0), v_getInfoState_4410_, v___f_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4416_, lean_object* v_s_4417_){
_start:
{
lean_object* v_assignment_4418_; lean_object* v_lazyAssignment_4419_; lean_object* v_trees_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_assignment_4418_ = lean_ctor_get(v_s_4417_, 0);
v_lazyAssignment_4419_ = lean_ctor_get(v_s_4417_, 1);
v_trees_4420_ = lean_ctor_get(v_s_4417_, 2);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_s_4417_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v_s_4417_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_trees_4420_);
lean_inc(v_lazyAssignment_4419_);
lean_inc(v_assignment_4418_);
lean_dec(v_s_4417_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_assignment_4418_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_lazyAssignment_4419_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_trees_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_ctor_set_uint8(v___x_4425_, sizeof(void*)*3, v_flag_4416_);
return v___x_4425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4428_, lean_object* v_s_4429_){
_start:
{
uint8_t v_flag_boxed_4430_; lean_object* v_res_4431_; 
v_flag_boxed_4430_ = lean_unbox(v_flag_4428_);
v_res_4431_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4430_, v_s_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4432_, uint8_t v_flag_4433_){
_start:
{
lean_object* v_modifyInfoState_4434_; lean_object* v___x_4435_; lean_object* v___f_4436_; lean_object* v___x_4437_; 
v_modifyInfoState_4434_ = lean_ctor_get(v_inst_4432_, 1);
lean_inc(v_modifyInfoState_4434_);
lean_dec_ref(v_inst_4432_);
v___x_4435_ = lean_box(v_flag_4433_);
v___f_4436_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4436_, 0, v___x_4435_);
v___x_4437_ = lean_apply_1(v_modifyInfoState_4434_, v___f_4436_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4438_, lean_object* v_flag_4439_){
_start:
{
uint8_t v_flag_boxed_4440_; lean_object* v_res_4441_; 
v_flag_boxed_4440_ = lean_unbox(v_flag_4439_);
v_res_4441_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4438_, v_flag_boxed_4440_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4442_, lean_object* v_inst_4443_, uint8_t v_flag_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4443_, v_flag_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4446_, lean_object* v_inst_4447_, lean_object* v_flag_4448_){
_start:
{
uint8_t v_flag_boxed_4449_; lean_object* v_res_4450_; 
v_flag_boxed_4449_ = lean_unbox(v_flag_4448_);
v_res_4450_ = l_Lean_Elab_enableInfoTree(v_m_4446_, v_inst_4447_, v_flag_boxed_4449_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4451_){
_start:
{
lean_object* v_fst_4452_; 
v_fst_4452_ = lean_ctor_get(v_x_4451_, 0);
lean_inc(v_fst_4452_);
return v_fst_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4453_);
lean_dec_ref(v_x_4453_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4455_, lean_object* v_____r_4456_){
_start:
{
lean_inc(v_x_4455_);
return v_x_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4457_, lean_object* v_____r_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4457_, v_____r_4458_);
lean_dec(v_x_4457_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4460_, lean_object* v_x_4461_){
_start:
{
lean_inc(v___x_4460_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4462_, lean_object* v_x_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4462_, v_x_4463_);
lean_dec(v_x_4463_);
lean_dec(v___x_4462_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4465_, lean_object* v_inst_4466_, uint8_t v_flag_4467_, lean_object* v_toBind_4468_, lean_object* v___f_4469_, lean_object* v_inst_4470_, lean_object* v___f_4471_, lean_object* v_____do__lift_4472_){
_start:
{
uint8_t v_enabled_4473_; lean_object* v_map_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___f_4478_; lean_object* v_y_4479_; lean_object* v___x_4480_; 
v_enabled_4473_ = lean_ctor_get_uint8(v_____do__lift_4472_, sizeof(void*)*3);
v_map_4474_ = lean_ctor_get(v_toFunctor_4465_, 0);
lean_inc(v_map_4474_);
lean_dec_ref(v_toFunctor_4465_);
lean_inc_ref(v_inst_4466_);
v___x_4475_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4466_, v_flag_4467_);
v___x_4476_ = lean_apply_4(v_toBind_4468_, lean_box(0), lean_box(0), v___x_4475_, v___f_4469_);
v___x_4477_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4466_, v_enabled_4473_);
v___f_4478_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4478_, 0, v___x_4477_);
v_y_4479_ = lean_apply_4(v_inst_4470_, lean_box(0), lean_box(0), v___x_4476_, v___f_4478_);
v___x_4480_ = lean_apply_4(v_map_4474_, lean_box(0), lean_box(0), v___f_4471_, v_y_4479_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4481_, lean_object* v_inst_4482_, lean_object* v_flag_4483_, lean_object* v_toBind_4484_, lean_object* v___f_4485_, lean_object* v_inst_4486_, lean_object* v___f_4487_, lean_object* v_____do__lift_4488_){
_start:
{
uint8_t v_flag_boxed_4489_; lean_object* v_res_4490_; 
v_flag_boxed_4489_ = lean_unbox(v_flag_4483_);
v_res_4490_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4481_, v_inst_4482_, v_flag_boxed_4489_, v_toBind_4484_, v___f_4485_, v_inst_4486_, v___f_4487_, v_____do__lift_4488_);
lean_dec_ref(v_____do__lift_4488_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4492_, lean_object* v_inst_4493_, lean_object* v_inst_4494_, uint8_t v_flag_4495_, lean_object* v_x_4496_){
_start:
{
lean_object* v_toApplicative_4497_; lean_object* v_toBind_4498_; lean_object* v_getInfoState_4499_; lean_object* v_toFunctor_4500_; lean_object* v___f_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; lean_object* v___f_4504_; lean_object* v___x_4505_; 
v_toApplicative_4497_ = lean_ctor_get(v_inst_4492_, 0);
lean_inc_ref(v_toApplicative_4497_);
v_toBind_4498_ = lean_ctor_get(v_inst_4492_, 1);
lean_inc_n(v_toBind_4498_, 2);
lean_dec_ref(v_inst_4492_);
v_getInfoState_4499_ = lean_ctor_get(v_inst_4493_, 0);
lean_inc(v_getInfoState_4499_);
v_toFunctor_4500_ = lean_ctor_get(v_toApplicative_4497_, 0);
lean_inc_ref(v_toFunctor_4500_);
lean_dec_ref(v_toApplicative_4497_);
v___f_4501_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4502_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4502_, 0, v_x_4496_);
v___x_4503_ = lean_box(v_flag_4495_);
v___f_4504_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4504_, 0, v_toFunctor_4500_);
lean_closure_set(v___f_4504_, 1, v_inst_4493_);
lean_closure_set(v___f_4504_, 2, v___x_4503_);
lean_closure_set(v___f_4504_, 3, v_toBind_4498_);
lean_closure_set(v___f_4504_, 4, v___f_4502_);
lean_closure_set(v___f_4504_, 5, v_inst_4494_);
lean_closure_set(v___f_4504_, 6, v___f_4501_);
v___x_4505_ = lean_apply_4(v_toBind_4498_, lean_box(0), lean_box(0), v_getInfoState_4499_, v___f_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4506_, lean_object* v_inst_4507_, lean_object* v_inst_4508_, lean_object* v_flag_4509_, lean_object* v_x_4510_){
_start:
{
uint8_t v_flag_boxed_4511_; lean_object* v_res_4512_; 
v_flag_boxed_4511_ = lean_unbox(v_flag_4509_);
v_res_4512_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4506_, v_inst_4507_, v_inst_4508_, v_flag_boxed_4511_, v_x_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4513_, lean_object* v_00_u03b1_4514_, lean_object* v_inst_4515_, lean_object* v_inst_4516_, lean_object* v_inst_4517_, uint8_t v_flag_4518_, lean_object* v_x_4519_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4515_, v_inst_4516_, v_inst_4517_, v_flag_4518_, v_x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4521_, lean_object* v_00_u03b1_4522_, lean_object* v_inst_4523_, lean_object* v_inst_4524_, lean_object* v_inst_4525_, lean_object* v_flag_4526_, lean_object* v_x_4527_){
_start:
{
uint8_t v_flag_boxed_4528_; lean_object* v_res_4529_; 
v_flag_boxed_4528_ = lean_unbox(v_flag_4526_);
v_res_4529_ = l_Lean_Elab_withEnableInfoTree(v_m_4521_, v_00_u03b1_4522_, v_inst_4523_, v_inst_4524_, v_inst_4525_, v_flag_boxed_4528_, v_x_4527_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4530_, lean_object* v_____do__lift_4531_){
_start:
{
lean_object* v_trees_4532_; lean_object* v___x_4533_; 
v_trees_4532_ = lean_ctor_get(v_____do__lift_4531_, 2);
lean_inc_ref(v_trees_4532_);
lean_dec_ref(v_____do__lift_4531_);
v___x_4533_ = lean_apply_2(v_toPure_4530_, lean_box(0), v_trees_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4534_, lean_object* v_inst_4535_){
_start:
{
lean_object* v_toApplicative_4536_; lean_object* v_toBind_4537_; lean_object* v_getInfoState_4538_; lean_object* v_toPure_4539_; lean_object* v___f_4540_; lean_object* v___x_4541_; 
v_toApplicative_4536_ = lean_ctor_get(v_inst_4535_, 0);
lean_inc_ref(v_toApplicative_4536_);
v_toBind_4537_ = lean_ctor_get(v_inst_4535_, 1);
lean_inc(v_toBind_4537_);
lean_dec_ref(v_inst_4535_);
v_getInfoState_4538_ = lean_ctor_get(v_inst_4534_, 0);
lean_inc(v_getInfoState_4538_);
lean_dec_ref(v_inst_4534_);
v_toPure_4539_ = lean_ctor_get(v_toApplicative_4536_, 1);
lean_inc(v_toPure_4539_);
lean_dec_ref(v_toApplicative_4536_);
v___f_4540_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4540_, 0, v_toPure_4539_);
v___x_4541_ = lean_apply_4(v_toBind_4537_, lean_box(0), lean_box(0), v_getInfoState_4538_, v___f_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4542_, lean_object* v_inst_4543_, lean_object* v_inst_4544_){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4543_, v_inst_4544_);
return v___x_4545_;
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
