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
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
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
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15;
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
lean_dec_ref(v_x_150_);
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
lean_dec_ref(v_x_150_);
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
lean_dec_ref(v_x_150_);
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
lean_dec_ref(v_x_150_);
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
lean_dec_ref(v_fst_331_);
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
lean_dec_ref(v_fst_339_);
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
lean_dec_ref(v_fst_350_);
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
lean_dec_ref(v_t_353_);
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
lean_dec_ref(v_t_353_);
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
lean_dec_ref(v_tree_459_);
v_val_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_val_483_);
lean_dec_ref(v___x_482_);
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
lean_dec_ref(v___x_1078_);
if (lean_obj_tag(v_val_1080_) == 1)
{
uint8_t v_v_1081_; 
v_v_1081_ = lean_ctor_get_uint8(v_val_1080_, 0);
lean_dec_ref(v_val_1080_);
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
lean_dec_ref(v___x_1092_);
if (lean_obj_tag(v_val_1093_) == 3)
{
lean_object* v_v_1094_; 
v_v_1094_ = lean_ctor_get(v_val_1093_, 0);
lean_inc(v_v_1094_);
lean_dec_ref(v_val_1093_);
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
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = l_Lean_Options_empty;
v___x_1134_ = l_Lean_Core_getMaxHeartbeats(v___x_1133_);
return v___x_1134_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = l_Lean_diagnostics;
v___x_1136_ = l_Lean_Options_empty;
v___x_1137_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_maxRecDepth;
v___x_1139_ = l_Lean_Options_empty;
v___x_1140_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_toCommandContextInfo_1148_; lean_object* v_env_1149_; lean_object* v_options_1150_; lean_object* v_currNamespace_1151_; lean_object* v_openDecls_1152_; lean_object* v_ngen_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v_fileName_1168_; lean_object* v_fileMap_1169_; lean_object* v_currRecDepth_1170_; lean_object* v_ref_1171_; lean_object* v_currNamespace_1172_; lean_object* v_openDecls_1173_; lean_object* v_initHeartbeats_1174_; lean_object* v_maxHeartbeats_1175_; lean_object* v_quotContext_1176_; lean_object* v_currMacroScope_1177_; lean_object* v_cancelTk_x3f_1178_; uint8_t v_suppressElabErrors_1179_; lean_object* v_inheritedTraceOptions_1180_; lean_object* v___y_1181_; lean_object* v___y_1214_; uint8_t v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_env_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___y_1271_; lean_object* v___y_1272_; uint8_t v___y_1302_; uint8_t v___x_1322_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_1146_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_1147_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_1148_ = lean_ctor_get(v_info_1141_, 0);
lean_inc_ref(v_toCommandContextInfo_1148_);
lean_dec_ref(v_info_1141_);
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
v___x_1161_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_1163_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1163_, 0, v_env_1157_);
lean_ctor_set(v___x_1163_, 1, v___x_1155_);
lean_ctor_set(v___x_1163_, 2, v_ngen_1153_);
lean_ctor_set(v___x_1163_, 3, v___x_1159_);
lean_ctor_set(v___x_1163_, 4, v___x_1160_);
lean_ctor_set(v___x_1163_, 5, v___x_1145_);
lean_ctor_set(v___x_1163_, 6, v___x_1146_);
lean_ctor_set(v___x_1163_, 7, v___x_1161_);
lean_ctor_set(v___x_1163_, 8, v___x_1162_);
v___x_1164_ = lean_st_mk_ref(v___x_1163_);
v___x_1256_ = l_Lean_inheritedTraceOptions;
v___x_1257_ = lean_st_ref_get(v___x_1256_);
v___x_1258_ = lean_st_ref_get(v___x_1164_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_1260_ = l_Lean_instInhabitedFileMap_default;
v___x_1261_ = l_Lean_Options_empty;
v___x_1262_ = lean_unsigned_to_nat(1000u);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1266_, 0, v___x_1259_);
lean_ctor_set(v___x_1266_, 1, v___x_1260_);
lean_ctor_set(v___x_1266_, 2, v___x_1261_);
lean_ctor_set(v___x_1266_, 3, v___x_1144_);
lean_ctor_set(v___x_1266_, 4, v___x_1262_);
lean_ctor_set(v___x_1266_, 5, v___x_1263_);
lean_ctor_set(v___x_1266_, 6, v_currNamespace_1151_);
lean_ctor_set(v___x_1266_, 7, v_openDecls_1152_);
lean_ctor_set(v___x_1266_, 8, v___x_1147_);
lean_ctor_set(v___x_1266_, 9, v___x_1264_);
lean_ctor_set(v___x_1266_, 10, v___x_1158_);
lean_ctor_set(v___x_1266_, 11, v___x_1154_);
lean_ctor_set(v___x_1266_, 12, v___x_1265_);
lean_ctor_set(v___x_1266_, 13, v___x_1257_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*14, v___x_1156_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*14 + 1, v___x_1156_);
v_env_1267_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_env_1267_);
lean_dec(v___x_1258_);
v___x_1268_ = l_Lean_diagnostics;
v___x_1269_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_1322_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1267_);
lean_dec_ref(v_env_1267_);
if (v___x_1322_ == 0)
{
if (v___x_1269_ == 0)
{
lean_inc(v___x_1164_);
v___y_1271_ = v___x_1266_;
v___y_1272_ = v___x_1164_;
goto v___jp_1270_;
}
else
{
v___y_1302_ = v___x_1322_;
goto v___jp_1301_;
}
}
else
{
v___y_1302_ = v___x_1269_;
goto v___jp_1301_;
}
v___jp_1165_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_1150_, v___y_1166_);
v___x_1183_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1183_, 0, v_fileName_1168_);
lean_ctor_set(v___x_1183_, 1, v_fileMap_1169_);
lean_ctor_set(v___x_1183_, 2, v_options_1150_);
lean_ctor_set(v___x_1183_, 3, v_currRecDepth_1170_);
lean_ctor_set(v___x_1183_, 4, v___x_1182_);
lean_ctor_set(v___x_1183_, 5, v_ref_1171_);
lean_ctor_set(v___x_1183_, 6, v_currNamespace_1172_);
lean_ctor_set(v___x_1183_, 7, v_openDecls_1173_);
lean_ctor_set(v___x_1183_, 8, v_initHeartbeats_1174_);
lean_ctor_set(v___x_1183_, 9, v_maxHeartbeats_1175_);
lean_ctor_set(v___x_1183_, 10, v_quotContext_1176_);
lean_ctor_set(v___x_1183_, 11, v_currMacroScope_1177_);
lean_ctor_set(v___x_1183_, 12, v_cancelTk_x3f_1178_);
lean_ctor_set(v___x_1183_, 13, v_inheritedTraceOptions_1180_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14, v___y_1167_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 1, v_suppressElabErrors_1179_);
v___x_1184_ = lean_apply_3(v_x_1142_, v___x_1183_, v___y_1181_, lean_box(0));
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1193_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_get(v___x_1164_);
lean_dec(v___x_1164_);
lean_dec(v___x_1189_);
if (v_isShared_1188_ == 0)
{
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1185_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v___x_1164_);
v_a_1194_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1196_ = v___x_1184_;
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1184_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
if (lean_obj_tag(v_a_1194_) == 0)
{
lean_object* v_msg_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_msg_1198_ = lean_ctor_get(v_a_1194_, 1);
lean_inc_ref(v_msg_1198_);
lean_dec_ref(v_a_1194_);
v___x_1199_ = l_Lean_MessageData_toString(v_msg_1198_);
v___x_1200_ = lean_mk_io_user_error(v___x_1199_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1200_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v_id_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v_id_1204_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_id_1204_);
lean_dec_ref(v_a_1194_);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_1206_ = l_Nat_reprFast(v_id_1204_);
v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = lean_mk_io_user_error(v___x_1207_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1208_);
v___x_1210_ = v___x_1196_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
v___jp_1213_:
{
lean_object* v_fileName_1218_; lean_object* v_fileMap_1219_; lean_object* v_currRecDepth_1220_; lean_object* v_ref_1221_; lean_object* v_currNamespace_1222_; lean_object* v_openDecls_1223_; lean_object* v_initHeartbeats_1224_; lean_object* v_maxHeartbeats_1225_; lean_object* v_quotContext_1226_; lean_object* v_currMacroScope_1227_; lean_object* v_cancelTk_x3f_1228_; uint8_t v_suppressElabErrors_1229_; lean_object* v_inheritedTraceOptions_1230_; 
v_fileName_1218_ = lean_ctor_get(v___y_1216_, 0);
lean_inc_ref(v_fileName_1218_);
v_fileMap_1219_ = lean_ctor_get(v___y_1216_, 1);
lean_inc_ref(v_fileMap_1219_);
v_currRecDepth_1220_ = lean_ctor_get(v___y_1216_, 3);
lean_inc(v_currRecDepth_1220_);
v_ref_1221_ = lean_ctor_get(v___y_1216_, 5);
lean_inc(v_ref_1221_);
v_currNamespace_1222_ = lean_ctor_get(v___y_1216_, 6);
lean_inc(v_currNamespace_1222_);
v_openDecls_1223_ = lean_ctor_get(v___y_1216_, 7);
lean_inc(v_openDecls_1223_);
v_initHeartbeats_1224_ = lean_ctor_get(v___y_1216_, 8);
lean_inc(v_initHeartbeats_1224_);
v_maxHeartbeats_1225_ = lean_ctor_get(v___y_1216_, 9);
lean_inc(v_maxHeartbeats_1225_);
v_quotContext_1226_ = lean_ctor_get(v___y_1216_, 10);
lean_inc(v_quotContext_1226_);
v_currMacroScope_1227_ = lean_ctor_get(v___y_1216_, 11);
lean_inc(v_currMacroScope_1227_);
v_cancelTk_x3f_1228_ = lean_ctor_get(v___y_1216_, 12);
lean_inc(v_cancelTk_x3f_1228_);
v_suppressElabErrors_1229_ = lean_ctor_get_uint8(v___y_1216_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1230_ = lean_ctor_get(v___y_1216_, 13);
lean_inc_ref(v_inheritedTraceOptions_1230_);
lean_dec_ref(v___y_1216_);
v___y_1166_ = v___y_1214_;
v___y_1167_ = v___y_1215_;
v_fileName_1168_ = v_fileName_1218_;
v_fileMap_1169_ = v_fileMap_1219_;
v_currRecDepth_1170_ = v_currRecDepth_1220_;
v_ref_1171_ = v_ref_1221_;
v_currNamespace_1172_ = v_currNamespace_1222_;
v_openDecls_1173_ = v_openDecls_1223_;
v_initHeartbeats_1174_ = v_initHeartbeats_1224_;
v_maxHeartbeats_1175_ = v_maxHeartbeats_1225_;
v_quotContext_1176_ = v_quotContext_1226_;
v_currMacroScope_1177_ = v_currMacroScope_1227_;
v_cancelTk_x3f_1178_ = v_cancelTk_x3f_1228_;
v_suppressElabErrors_1179_ = v_suppressElabErrors_1229_;
v_inheritedTraceOptions_1180_ = v_inheritedTraceOptions_1230_;
v___y_1181_ = v___y_1217_;
goto v___jp_1165_;
}
v___jp_1231_:
{
if (v___y_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v_env_1238_; lean_object* v_nextMacroScope_1239_; lean_object* v_ngen_1240_; lean_object* v_auxDeclNGen_1241_; lean_object* v_traceState_1242_; lean_object* v_messages_1243_; lean_object* v_infoState_1244_; lean_object* v_snapshotTasks_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1254_; 
v___x_1237_ = lean_st_ref_take(v___y_1235_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
v_nextMacroScope_1239_ = lean_ctor_get(v___x_1237_, 1);
v_ngen_1240_ = lean_ctor_get(v___x_1237_, 2);
v_auxDeclNGen_1241_ = lean_ctor_get(v___x_1237_, 3);
v_traceState_1242_ = lean_ctor_get(v___x_1237_, 4);
v_messages_1243_ = lean_ctor_get(v___x_1237_, 6);
v_infoState_1244_ = lean_ctor_get(v___x_1237_, 7);
v_snapshotTasks_1245_ = lean_ctor_get(v___x_1237_, 8);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1237_, 5);
lean_dec(v_unused_1255_);
v___x_1247_ = v___x_1237_;
v_isShared_1248_ = v_isSharedCheck_1254_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snapshotTasks_1245_);
lean_inc(v_infoState_1244_);
lean_inc(v_messages_1243_);
lean_inc(v_traceState_1242_);
lean_inc(v_auxDeclNGen_1241_);
lean_inc(v_ngen_1240_);
lean_inc(v_nextMacroScope_1239_);
lean_inc(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1254_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = l_Lean_Kernel_enableDiag(v_env_1238_, v___y_1234_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 5, v___x_1145_);
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_nextMacroScope_1239_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_ngen_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_auxDeclNGen_1241_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v_traceState_1242_);
lean_ctor_set(v_reuseFailAlloc_1253_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1253_, 6, v_messages_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 7, v_infoState_1244_);
lean_ctor_set(v_reuseFailAlloc_1253_, 8, v_snapshotTasks_1245_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_st_ref_set(v___y_1235_, v___x_1251_);
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___y_1234_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1235_;
goto v___jp_1213_;
}
}
}
else
{
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___y_1234_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1235_;
goto v___jp_1213_;
}
}
v___jp_1270_:
{
lean_object* v___x_1273_; lean_object* v_fileName_1274_; lean_object* v_fileMap_1275_; lean_object* v_currRecDepth_1276_; lean_object* v_ref_1277_; lean_object* v_currNamespace_1278_; lean_object* v_openDecls_1279_; lean_object* v_initHeartbeats_1280_; lean_object* v_maxHeartbeats_1281_; lean_object* v_quotContext_1282_; lean_object* v_currMacroScope_1283_; lean_object* v_cancelTk_x3f_1284_; uint8_t v_suppressElabErrors_1285_; lean_object* v_inheritedTraceOptions_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1298_; 
v___x_1273_ = lean_st_ref_get(v___y_1272_);
v_fileName_1274_ = lean_ctor_get(v___y_1271_, 0);
v_fileMap_1275_ = lean_ctor_get(v___y_1271_, 1);
v_currRecDepth_1276_ = lean_ctor_get(v___y_1271_, 3);
v_ref_1277_ = lean_ctor_get(v___y_1271_, 5);
v_currNamespace_1278_ = lean_ctor_get(v___y_1271_, 6);
v_openDecls_1279_ = lean_ctor_get(v___y_1271_, 7);
v_initHeartbeats_1280_ = lean_ctor_get(v___y_1271_, 8);
v_maxHeartbeats_1281_ = lean_ctor_get(v___y_1271_, 9);
v_quotContext_1282_ = lean_ctor_get(v___y_1271_, 10);
v_currMacroScope_1283_ = lean_ctor_get(v___y_1271_, 11);
v_cancelTk_x3f_1284_ = lean_ctor_get(v___y_1271_, 12);
v_suppressElabErrors_1285_ = lean_ctor_get_uint8(v___y_1271_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1286_ = lean_ctor_get(v___y_1271_, 13);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1271_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; lean_object* v_unused_1300_; 
v_unused_1299_ = lean_ctor_get(v___y_1271_, 4);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v___y_1271_, 2);
lean_dec(v_unused_1300_);
v___x_1288_ = v___y_1271_;
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_inheritedTraceOptions_1286_);
lean_inc(v_cancelTk_x3f_1284_);
lean_inc(v_currMacroScope_1283_);
lean_inc(v_quotContext_1282_);
lean_inc(v_maxHeartbeats_1281_);
lean_inc(v_initHeartbeats_1280_);
lean_inc(v_openDecls_1279_);
lean_inc(v_currNamespace_1278_);
lean_inc(v_ref_1277_);
lean_inc(v_currRecDepth_1276_);
lean_inc(v_fileMap_1275_);
lean_inc(v_fileName_1274_);
lean_dec(v___y_1271_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_env_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v_env_1290_ = lean_ctor_get(v___x_1273_, 0);
lean_inc_ref(v_env_1290_);
lean_dec(v___x_1273_);
v___x_1291_ = l_Lean_maxRecDepth;
v___x_1292_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
lean_inc_ref(v_inheritedTraceOptions_1286_);
lean_inc(v_cancelTk_x3f_1284_);
lean_inc(v_currMacroScope_1283_);
lean_inc(v_quotContext_1282_);
lean_inc(v_maxHeartbeats_1281_);
lean_inc(v_initHeartbeats_1280_);
lean_inc(v_openDecls_1279_);
lean_inc(v_currNamespace_1278_);
lean_inc(v_ref_1277_);
lean_inc(v_currRecDepth_1276_);
lean_inc_ref(v_fileMap_1275_);
lean_inc_ref(v_fileName_1274_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 4, v___x_1292_);
lean_ctor_set(v___x_1288_, 2, v___x_1261_);
v___x_1294_ = v___x_1288_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_fileName_1274_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_fileMap_1275_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_currRecDepth_1276_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1297_, 5, v_ref_1277_);
lean_ctor_set(v_reuseFailAlloc_1297_, 6, v_currNamespace_1278_);
lean_ctor_set(v_reuseFailAlloc_1297_, 7, v_openDecls_1279_);
lean_ctor_set(v_reuseFailAlloc_1297_, 8, v_initHeartbeats_1280_);
lean_ctor_set(v_reuseFailAlloc_1297_, 9, v_maxHeartbeats_1281_);
lean_ctor_set(v_reuseFailAlloc_1297_, 10, v_quotContext_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 11, v_currMacroScope_1283_);
lean_ctor_set(v_reuseFailAlloc_1297_, 12, v_cancelTk_x3f_1284_);
lean_ctor_set(v_reuseFailAlloc_1297_, 13, v_inheritedTraceOptions_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*14 + 1, v_suppressElabErrors_1285_);
v___x_1294_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
uint8_t v___x_1295_; uint8_t v___x_1296_; 
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*14, v___x_1269_);
v___x_1295_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_1150_, v___x_1268_);
v___x_1296_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1290_);
lean_dec_ref(v_env_1290_);
if (v___x_1296_ == 0)
{
if (v___x_1295_ == 0)
{
lean_dec_ref(v___x_1294_);
v___y_1166_ = v___x_1291_;
v___y_1167_ = v___x_1295_;
v_fileName_1168_ = v_fileName_1274_;
v_fileMap_1169_ = v_fileMap_1275_;
v_currRecDepth_1170_ = v_currRecDepth_1276_;
v_ref_1171_ = v_ref_1277_;
v_currNamespace_1172_ = v_currNamespace_1278_;
v_openDecls_1173_ = v_openDecls_1279_;
v_initHeartbeats_1174_ = v_initHeartbeats_1280_;
v_maxHeartbeats_1175_ = v_maxHeartbeats_1281_;
v_quotContext_1176_ = v_quotContext_1282_;
v_currMacroScope_1177_ = v_currMacroScope_1283_;
v_cancelTk_x3f_1178_ = v_cancelTk_x3f_1284_;
v_suppressElabErrors_1179_ = v_suppressElabErrors_1285_;
v_inheritedTraceOptions_1180_ = v_inheritedTraceOptions_1286_;
v___y_1181_ = v___y_1272_;
goto v___jp_1165_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1286_);
lean_dec(v_cancelTk_x3f_1284_);
lean_dec(v_currMacroScope_1283_);
lean_dec(v_quotContext_1282_);
lean_dec(v_maxHeartbeats_1281_);
lean_dec(v_initHeartbeats_1280_);
lean_dec(v_openDecls_1279_);
lean_dec(v_currNamespace_1278_);
lean_dec(v_ref_1277_);
lean_dec(v_currRecDepth_1276_);
lean_dec_ref(v_fileMap_1275_);
lean_dec_ref(v_fileName_1274_);
v___y_1232_ = v___x_1291_;
v___y_1233_ = v___x_1294_;
v___y_1234_ = v___x_1295_;
v___y_1235_ = v___y_1272_;
v___y_1236_ = v___x_1296_;
goto v___jp_1231_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1286_);
lean_dec(v_cancelTk_x3f_1284_);
lean_dec(v_currMacroScope_1283_);
lean_dec(v_quotContext_1282_);
lean_dec(v_maxHeartbeats_1281_);
lean_dec(v_initHeartbeats_1280_);
lean_dec(v_openDecls_1279_);
lean_dec(v_currNamespace_1278_);
lean_dec(v_ref_1277_);
lean_dec(v_currRecDepth_1276_);
lean_dec_ref(v_fileMap_1275_);
lean_dec_ref(v_fileName_1274_);
v___y_1232_ = v___x_1291_;
v___y_1233_ = v___x_1294_;
v___y_1234_ = v___x_1295_;
v___y_1235_ = v___y_1272_;
v___y_1236_ = v___x_1295_;
goto v___jp_1231_;
}
}
}
}
v___jp_1301_:
{
if (v___y_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v_env_1304_; lean_object* v_nextMacroScope_1305_; lean_object* v_ngen_1306_; lean_object* v_auxDeclNGen_1307_; lean_object* v_traceState_1308_; lean_object* v_messages_1309_; lean_object* v_infoState_1310_; lean_object* v_snapshotTasks_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1320_; 
v___x_1303_ = lean_st_ref_take(v___x_1164_);
v_env_1304_ = lean_ctor_get(v___x_1303_, 0);
v_nextMacroScope_1305_ = lean_ctor_get(v___x_1303_, 1);
v_ngen_1306_ = lean_ctor_get(v___x_1303_, 2);
v_auxDeclNGen_1307_ = lean_ctor_get(v___x_1303_, 3);
v_traceState_1308_ = lean_ctor_get(v___x_1303_, 4);
v_messages_1309_ = lean_ctor_get(v___x_1303_, 6);
v_infoState_1310_ = lean_ctor_get(v___x_1303_, 7);
v_snapshotTasks_1311_ = lean_ctor_get(v___x_1303_, 8);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1303_, 5);
lean_dec(v_unused_1321_);
v___x_1313_ = v___x_1303_;
v_isShared_1314_ = v_isSharedCheck_1320_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snapshotTasks_1311_);
lean_inc(v_infoState_1310_);
lean_inc(v_messages_1309_);
lean_inc(v_traceState_1308_);
lean_inc(v_auxDeclNGen_1307_);
lean_inc(v_ngen_1306_);
lean_inc(v_nextMacroScope_1305_);
lean_inc(v_env_1304_);
lean_dec(v___x_1303_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1320_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l_Lean_Kernel_enableDiag(v_env_1304_, v___x_1269_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 5, v___x_1145_);
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_nextMacroScope_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_ngen_1306_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_auxDeclNGen_1307_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_traceState_1308_);
lean_ctor_set(v_reuseFailAlloc_1319_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1319_, 6, v_messages_1309_);
lean_ctor_set(v_reuseFailAlloc_1319_, 7, v_infoState_1310_);
lean_ctor_set(v_reuseFailAlloc_1319_, 8, v_snapshotTasks_1311_);
v___x_1317_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_st_ref_set(v___x_1164_, v___x_1317_);
lean_inc(v___x_1164_);
v___y_1271_ = v___x_1266_;
v___y_1272_ = v___x_1164_;
goto v___jp_1270_;
}
}
}
else
{
lean_inc(v___x_1164_);
v___y_1271_ = v___x_1266_;
v___y_1272_ = v___x_1164_;
goto v___jp_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_1323_, lean_object* v_x_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1323_, v_x_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_1327_, lean_object* v_info_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1328_, v_x_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_info_1333_, lean_object* v_x_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_1332_, v_info_1333_, v_x_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_1337_, lean_object* v_x_1338_, lean_object* v___x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_st_mk_ref(v___x_1337_);
lean_inc(v___x_1343_);
v___x_1344_ = lean_apply_5(v_x_1338_, v___x_1339_, v___x_1343_, v___y_1340_, v___y_1341_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1354_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_st_ref_get(v___x_1343_);
lean_dec(v___x_1343_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1345_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v___x_1343_);
v_a_1355_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1344_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1344_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_1363_, lean_object* v_x_1364_, lean_object* v___x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_1363_, v_x_1364_, v___x_1365_, v___y_1366_, v___y_1367_);
return v_res_1369_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1376_; uint64_t v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1377_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1380_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set_uint64(v___x_1380_, sizeof(void*)*1, v___x_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1387_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
lean_ctor_set(v___x_1387_, 3, v___x_1386_);
lean_ctor_set(v___x_1387_, 4, v___x_1386_);
lean_ctor_set(v___x_1387_, 5, v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_unsigned_to_nat(32u);
v___x_1389_ = lean_mk_empty_array_with_capacity(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = ((size_t)5ULL);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_unsigned_to_nat(32u);
v___x_1394_ = lean_mk_empty_array_with_capacity(v___x_1393_);
v___x_1395_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_1396_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___x_1394_);
lean_ctor_set(v___x_1396_, 2, v___x_1392_);
lean_ctor_set(v___x_1396_, 3, v___x_1392_);
lean_ctor_set_usize(v___x_1396_, 4, v___x_1391_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
lean_ctor_set(v___x_1398_, 2, v___x_1397_);
lean_ctor_set(v___x_1398_, 3, v___x_1397_);
lean_ctor_set(v___x_1398_, 4, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_1399_, lean_object* v_lctx_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_toCommandContextInfo_1411_; lean_object* v_mctx_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; 
v___x_1403_ = lean_box(1);
v___x_1404_ = 0;
v___x_1405_ = 1;
v___x_1406_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1410_, 0, v___x_1406_);
lean_ctor_set(v___x_1410_, 1, v___x_1403_);
lean_ctor_set(v___x_1410_, 2, v_lctx_1400_);
lean_ctor_set(v___x_1410_, 3, v___x_1408_);
lean_ctor_set(v___x_1410_, 4, v___x_1409_);
lean_ctor_set(v___x_1410_, 5, v___x_1407_);
lean_ctor_set(v___x_1410_, 6, v___x_1409_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*7, v___x_1404_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*7 + 1, v___x_1404_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*7 + 2, v___x_1404_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*7 + 3, v___x_1405_);
v_toCommandContextInfo_1411_ = lean_ctor_get(v_info_1399_, 0);
v_mctx_1412_ = lean_ctor_get(v_toCommandContextInfo_1411_, 3);
v___x_1413_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_1414_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_1412_);
v___x_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1416_, 0, v_mctx_1412_);
lean_ctor_set(v___x_1416_, 1, v___x_1413_);
lean_ctor_set(v___x_1416_, 2, v___x_1403_);
lean_ctor_set(v___x_1416_, 3, v___x_1414_);
lean_ctor_set(v___x_1416_, 4, v___x_1415_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1417_, 0, v___x_1416_);
lean_closure_set(v___f_1417_, 1, v_x_1401_);
lean_closure_set(v___f_1417_, 2, v___x_1410_);
v___x_1418_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1399_, v___f_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_fst_1423_; lean_object* v___x_1425_; 
v_fst_1423_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_fst_1423_);
lean_dec(v_a_1419_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_fst_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_fst_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1418_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1418_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_1436_, lean_object* v_lctx_1437_, lean_object* v_x_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1436_, v_lctx_1437_, v_x_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_1441_, lean_object* v_info_1442_, lean_object* v_lctx_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1442_, v_lctx_1443_, v_x_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_info_1448_, lean_object* v_lctx_1449_, lean_object* v_x_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_1447_, v_info_1448_, v_lctx_1449_, v_x_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_1453_, lean_object* v_lctx_1454_){
_start:
{
lean_object* v_toCommandContextInfo_1455_; lean_object* v_env_1456_; lean_object* v_mctx_1457_; lean_object* v_options_1458_; lean_object* v_currNamespace_1459_; lean_object* v_openDecls_1460_; lean_object* v___x_1461_; 
v_toCommandContextInfo_1455_ = lean_ctor_get(v_info_1453_, 0);
v_env_1456_ = lean_ctor_get(v_toCommandContextInfo_1455_, 0);
v_mctx_1457_ = lean_ctor_get(v_toCommandContextInfo_1455_, 3);
v_options_1458_ = lean_ctor_get(v_toCommandContextInfo_1455_, 4);
v_currNamespace_1459_ = lean_ctor_get(v_toCommandContextInfo_1455_, 5);
v_openDecls_1460_ = lean_ctor_get(v_toCommandContextInfo_1455_, 6);
lean_inc(v_openDecls_1460_);
lean_inc(v_currNamespace_1459_);
lean_inc_ref(v_options_1458_);
lean_inc_ref(v_mctx_1457_);
lean_inc_ref(v_env_1456_);
v___x_1461_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1461_, 0, v_env_1456_);
lean_ctor_set(v___x_1461_, 1, v_mctx_1457_);
lean_ctor_set(v___x_1461_, 2, v_lctx_1454_);
lean_ctor_set(v___x_1461_, 3, v_options_1458_);
lean_ctor_set(v___x_1461_, 4, v_currNamespace_1459_);
lean_ctor_set(v___x_1461_, 5, v_openDecls_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_1462_, lean_object* v_lctx_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1462_, v_lctx_1463_);
lean_dec_ref(v_info_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_1465_, lean_object* v_lctx_1466_, lean_object* v_stx_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1465_, v_lctx_1466_);
v___x_1470_ = l_Lean_ppTerm(v___x_1469_, v_stx_1467_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_1472_, lean_object* v_lctx_1473_, lean_object* v_stx_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_1472_, v_lctx_1473_, v_stx_1474_);
lean_dec_ref(v_info_1472_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_1492_, lean_object* v_pos_1493_, lean_object* v_info_1494_){
_start:
{
lean_object* v_toCommandContextInfo_1495_; lean_object* v_fileMap_1496_; lean_object* v___x_1497_; lean_object* v_line_1498_; lean_object* v_column_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1522_; 
v_toCommandContextInfo_1495_ = lean_ctor_get(v_ctx_1492_, 0);
lean_inc_ref(v_toCommandContextInfo_1495_);
lean_dec_ref(v_ctx_1492_);
v_fileMap_1496_ = lean_ctor_get(v_toCommandContextInfo_1495_, 2);
lean_inc_ref(v_fileMap_1496_);
lean_dec_ref(v_toCommandContextInfo_1495_);
v___x_1497_ = l_Lean_FileMap_toPosition(v_fileMap_1496_, v_pos_1493_);
v_line_1498_ = lean_ctor_get(v___x_1497_, 0);
v_column_1499_ = lean_ctor_get(v___x_1497_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1501_ = v___x_1497_;
v_isShared_1502_ = v_isSharedCheck_1522_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_column_1499_);
lean_inc(v_line_1498_);
lean_dec(v___x_1497_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1522_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1504_ = l_Nat_reprFast(v_line_1498_);
v___x_1505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 5);
lean_ctor_set(v___x_1501_, 1, v___x_1505_);
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1507_ = v___x_1501_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_pos_1514_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_1509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_Nat_reprFast(v_column_1499_);
v___x_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1509_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_1514_, 0, v___x_1512_);
lean_ctor_set(v_pos_1514_, 1, v___x_1513_);
switch(lean_obj_tag(v_info_1494_))
{
case 0:
{
return v_pos_1514_;
}
case 1:
{
uint8_t v_canonical_1518_; 
v_canonical_1518_ = lean_ctor_get_uint8(v_info_1494_, sizeof(void*)*2);
if (v_canonical_1518_ == 1)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_pos_1514_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
return v___x_1520_;
}
else
{
goto v___jp_1515_;
}
}
default: 
{
goto v___jp_1515_;
}
}
v___jp_1515_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_pos_1514_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_1523_, lean_object* v_pos_1524_, lean_object* v_info_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1523_, v_pos_1524_, v_info_1525_);
lean_dec(v_info_1525_);
lean_dec(v_pos_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_1530_, lean_object* v_stx_1531_){
_start:
{
lean_object* v___y_1533_; lean_object* v___y_1534_; uint8_t v___x_1542_; lean_object* v___y_1544_; lean_object* v___x_1547_; 
v___x_1542_ = 0;
v___x_1547_ = l_Lean_Syntax_getPos_x3f(v_stx_1531_, v___x_1542_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v___y_1544_ = v___x_1548_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1549_);
lean_dec_ref(v___x_1547_);
v___y_1544_ = v_val_1549_;
goto v___jp_1543_;
}
v___jp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1535_ = l_Lean_Syntax_getHeadInfo(v_stx_1531_);
lean_inc_ref(v_ctx_1530_);
v___x_1536_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1530_, v___y_1533_, v___x_1535_);
lean_dec(v___x_1535_);
lean_dec(v___y_1533_);
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_Syntax_getTailInfo(v_stx_1531_);
v___x_1540_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1530_, v___y_1534_, v___x_1539_);
lean_dec(v___x_1539_);
lean_dec(v___y_1534_);
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1538_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
return v___x_1541_;
}
v___jp_1543_:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1531_, v___x_1542_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_inc(v___y_1544_);
v___y_1533_ = v___y_1544_;
v___y_1534_ = v___y_1544_;
goto v___jp_1532_;
}
else
{
lean_object* v_val_1546_; 
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref(v___x_1545_);
v___y_1533_ = v___y_1544_;
v___y_1534_ = v_val_1546_;
goto v___jp_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_1550_, lean_object* v_stx_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1550_, v_stx_1551_);
lean_dec(v_stx_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_1556_, lean_object* v_info_1557_){
_start:
{
lean_object* v_elaborator_1558_; lean_object* v_stx_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1574_; 
v_elaborator_1558_ = lean_ctor_get(v_info_1557_, 0);
v_stx_1559_ = lean_ctor_get(v_info_1557_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_info_1557_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1561_ = v_info_1557_;
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_stx_1559_);
lean_inc(v_elaborator_1558_);
lean_dec(v_info_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v___x_1563_; 
v___x_1563_ = l_Lean_Name_isAnonymous(v_elaborator_1558_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1556_, v_stx_1559_);
lean_dec(v_stx_1559_);
v___x_1565_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 5);
lean_ctor_set(v___x_1561_, 1, v___x_1565_);
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1567_ = v___x_1561_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = 1;
v___x_1569_ = l_Lean_Name_toString(v_elaborator_1558_, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1567_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
return v___x_1571_;
}
}
else
{
lean_object* v___x_1573_; 
lean_del_object(v___x_1561_);
lean_dec(v_elaborator_1558_);
v___x_1573_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1556_, v_stx_1559_);
lean_dec(v_stx_1559_);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_1575_, lean_object* v_ctx_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v_lctx_1579_; lean_object* v___x_1580_; 
v_lctx_1579_ = lean_ctor_get(v_info_1575_, 1);
lean_inc_ref(v_lctx_1579_);
lean_dec_ref(v_info_1575_);
v___x_1580_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1576_, v_lctx_1579_, v_x_1577_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_1581_, lean_object* v_ctx_1582_, lean_object* v_x_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1581_, v_ctx_1582_, v_x_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_1586_, lean_object* v_info_1587_, lean_object* v_ctx_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1587_, v_ctx_1588_, v_x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_info_1593_, lean_object* v_ctx_1594_, lean_object* v_x_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_1592_, v_info_1593_, v_ctx_1594_, v_x_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_1612_, lean_object* v_toElabInfo_1613_, lean_object* v_expr_1614_, uint8_t v_isBinder_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v_a_1636_; lean_object* v___y_1646_; uint8_t v___y_1647_; lean_object* v___y_1650_; lean_object* v_a_1651_; lean_object* v___x_1654_; 
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc_ref(v_expr_1614_);
v___x_1654_ = lean_infer_type(v_expr_1614_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref(v___x_1654_);
v___x_1656_ = l_Lean_Meta_ppExpr(v_a_1655_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v_a_1636_ = v_a_1657_;
goto v___jp_1635_;
}
else
{
lean_object* v_a_1658_; 
v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1658_);
v___y_1650_ = v___x_1656_;
v_a_1651_ = v_a_1658_;
goto v___jp_1649_;
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1654_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1654_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
lean_inc(v_a_1659_);
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
v___y_1650_ = v___x_1664_;
v_a_1651_ = v_a_1659_;
goto v___jp_1649_;
}
}
}
v___jp_1621_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_inc_ref(v___y_1624_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1624_);
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1623_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v___y_1622_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1612_, v_toElabInfo_1613_);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
v___jp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_ppExpr(v_expr_1614_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_1640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_a_1638_);
v___x_1641_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
if (v_isBinder_1615_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_1622_ = v_a_1636_;
v___y_1623_ = v___x_1642_;
v___y_1624_ = v___x_1643_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_1622_ = v_a_1636_;
v___y_1623_ = v___x_1642_;
v___y_1624_ = v___x_1644_;
goto v___jp_1621_;
}
}
else
{
lean_dec(v_a_1636_);
lean_dec_ref(v_toElabInfo_1613_);
lean_dec_ref(v_ctx_1612_);
return v___x_1637_;
}
}
v___jp_1645_:
{
if (v___y_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v___y_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_1636_ = v___x_1648_;
goto v___jp_1635_;
}
else
{
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v_expr_1614_);
lean_dec_ref(v_toElabInfo_1613_);
lean_dec_ref(v_ctx_1612_);
return v___y_1646_;
}
}
v___jp_1649_:
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Lean_Exception_isInterrupt(v_a_1651_);
if (v___x_1652_ == 0)
{
uint8_t v___x_1653_; 
v___x_1653_ = l_Lean_Exception_isRuntime(v_a_1651_);
v___y_1646_ = v___y_1650_;
v___y_1647_ = v___x_1653_;
goto v___jp_1645_;
}
else
{
lean_dec_ref(v_a_1651_);
v___y_1646_ = v___y_1650_;
v___y_1647_ = v___x_1652_;
goto v___jp_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_1667_, lean_object* v_toElabInfo_1668_, lean_object* v_expr_1669_, lean_object* v_isBinder_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_isBinder_boxed_1676_; lean_object* v_res_1677_; 
v_isBinder_boxed_1676_ = lean_unbox(v_isBinder_1670_);
v_res_1677_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_1667_, v_toElabInfo_1668_, v_expr_1669_, v_isBinder_boxed_1676_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_1678_, lean_object* v_info_1679_){
_start:
{
lean_object* v_toElabInfo_1681_; lean_object* v_expr_1682_; uint8_t v_isBinder_1683_; lean_object* v___x_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; 
v_toElabInfo_1681_ = lean_ctor_get(v_info_1679_, 0);
v_expr_1682_ = lean_ctor_get(v_info_1679_, 3);
v_isBinder_1683_ = lean_ctor_get_uint8(v_info_1679_, sizeof(void*)*4);
v___x_1684_ = lean_box(v_isBinder_1683_);
lean_inc_ref(v_expr_1682_);
lean_inc_ref(v_toElabInfo_1681_);
lean_inc_ref(v_ctx_1678_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1685_, 0, v_ctx_1678_);
lean_closure_set(v___f_1685_, 1, v_toElabInfo_1681_);
lean_closure_set(v___f_1685_, 2, v_expr_1682_);
lean_closure_set(v___f_1685_, 3, v___x_1684_);
v___x_1686_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1679_, v_ctx_1678_, v___f_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_1687_, lean_object* v_info_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Elab_TermInfo_format(v_ctx_1687_, v_info_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_1694_, lean_object* v_info_1695_){
_start:
{
lean_object* v_toElabInfo_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_toElabInfo_1696_ = lean_ctor_get(v_info_1695_, 0);
lean_inc_ref(v_toElabInfo_1696_);
lean_dec_ref(v_info_1695_);
v___x_1697_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_1698_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1694_, v_toElabInfo_1696_);
v___x_1699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_1706_){
_start:
{
if (lean_obj_tag(v_x_1706_) == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1707_;
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1718_; 
v_val_1708_ = lean_ctor_get(v_x_1706_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1706_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1710_ = v_x_1706_;
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_val_1708_);
lean_dec(v_x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1713_ = lean_expr_dbg_to_string(v_val_1708_);
lean_dec(v_val_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 3);
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1712_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_1725_, lean_object* v_lctx_1726_, lean_object* v_stx_1727_, lean_object* v_expectedType_x3f_1728_, lean_object* v_info_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1754_; 
v___x_1735_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1725_, v_lctx_1726_, v_stx_1727_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1754_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1754_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1740_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_1741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_a_1736_);
v___x_1742_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1728_);
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = l_Lean_Elab_CompletionInfo_stx(v_info_1729_);
v___x_1749_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1725_, v___x_1748_);
lean_dec(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1747_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1750_);
v___x_1752_ = v___x_1738_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_1755_, lean_object* v_lctx_1756_, lean_object* v_stx_1757_, lean_object* v_expectedType_x3f_1758_, lean_object* v_info_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_1755_, v_lctx_1756_, v_stx_1757_, v_expectedType_x3f_1758_, v_info_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v_info_1759_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_1772_, lean_object* v_info_1773_){
_start:
{
switch(lean_obj_tag(v_info_1773_))
{
case 0:
{
lean_object* v_termInfo_1775_; lean_object* v_expectedType_x3f_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1797_; 
v_termInfo_1775_ = lean_ctor_get(v_info_1773_, 0);
v_expectedType_x3f_1776_ = lean_ctor_get(v_info_1773_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_info_1773_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1778_ = v_info_1773_;
v_isShared_1779_ = v_isSharedCheck_1797_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_expectedType_x3f_1776_);
lean_inc(v_termInfo_1775_);
lean_dec(v_info_1773_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1797_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Elab_TermInfo_format(v_ctx_1772_, v_termInfo_1775_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1796_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1796_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1796_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 5);
lean_ctor_set(v___x_1778_, 1, v_a_1781_);
lean_ctor_set(v___x_1778_, 0, v___x_1785_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_a_1781_);
v___x_1787_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1788_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1776_);
v___x_1791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1791_);
v___x_1793_ = v___x_1783_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_del_object(v___x_1778_);
lean_dec(v_expectedType_x3f_1776_);
return v___x_1780_;
}
}
}
case 1:
{
lean_object* v_stx_1798_; lean_object* v_lctx_1799_; lean_object* v_expectedType_x3f_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; 
v_stx_1798_ = lean_ctor_get(v_info_1773_, 0);
lean_inc(v_stx_1798_);
v_lctx_1799_ = lean_ctor_get(v_info_1773_, 2);
lean_inc_ref_n(v_lctx_1799_, 2);
v_expectedType_x3f_1800_ = lean_ctor_get(v_info_1773_, 3);
lean_inc(v_expectedType_x3f_1800_);
lean_inc_ref(v_ctx_1772_);
v___f_1801_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1801_, 0, v_ctx_1772_);
lean_closure_set(v___f_1801_, 1, v_lctx_1799_);
lean_closure_set(v___f_1801_, 2, v_stx_1798_);
lean_closure_set(v___f_1801_, 3, v_expectedType_x3f_1800_);
lean_closure_set(v___f_1801_, 4, v_info_1773_);
v___x_1802_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1772_, v_lctx_1799_, v___f_1801_);
return v___x_1802_;
}
default: 
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1803_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_1804_ = l_Lean_Elab_CompletionInfo_stx(v_info_1773_);
lean_dec_ref(v_info_1773_);
v___x_1805_ = lean_box(0);
v___x_1806_ = 0;
lean_inc(v___x_1804_);
v___x_1807_ = l_Lean_Syntax_formatStx(v___x_1804_, v___x_1805_, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1772_, v___x_1804_);
lean_dec(v___x_1804_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_1814_, lean_object* v_info_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1814_, v_info_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_1821_, lean_object* v_info_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1824_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_1825_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1821_, v_info_1822_);
v___x_1826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_1828_, lean_object* v_info_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Elab_CommandInfo_format(v_ctx_1828_, v_info_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_1835_, lean_object* v_info_1836_){
_start:
{
lean_object* v_stx_1838_; lean_object* v_optionName_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_stx_1838_ = lean_ctor_get(v_info_1836_, 0);
lean_inc(v_stx_1838_);
v_optionName_1839_ = lean_ctor_get(v_info_1836_, 1);
lean_inc(v_optionName_1839_);
lean_dec_ref(v_info_1836_);
v___x_1840_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_1841_ = 1;
v___x_1842_ = l_Lean_Name_toString(v_optionName_1839_, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1835_, v_stx_1838_);
lean_dec(v_stx_1838_);
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_1850_, lean_object* v_info_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_OptionInfo_format(v_ctx_1850_, v_info_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_1857_, lean_object* v_info_1858_){
_start:
{
lean_object* v_stx_1860_; lean_object* v_errorName_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1877_; 
v_stx_1860_ = lean_ctor_get(v_info_1858_, 0);
v_errorName_1861_ = lean_ctor_get(v_info_1858_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_info_1858_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1863_ = v_info_1858_;
v_isShared_1864_ = v_isSharedCheck_1877_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_errorName_1861_);
lean_inc(v_stx_1860_);
lean_dec(v_info_1858_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1877_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1865_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_1866_ = 1;
v___x_1867_ = l_Lean_Name_toString(v_errorName_1861_, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 5);
lean_ctor_set(v___x_1863_, 1, v___x_1868_);
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1870_ = v___x_1863_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1857_, v_stx_1860_);
lean_dec(v_stx_1860_);
v___x_1874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_1878_, lean_object* v_info_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1878_, v_info_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1888_, lean_object* v_fieldName_1889_, lean_object* v_ctx_1890_, lean_object* v_stx_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc_ref(v_val_1888_);
v___x_1897_ = lean_infer_type(v_val_1888_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_Meta_ppExpr(v_a_1898_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1930_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_ppExpr(v_val_1888_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1929_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1909_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1910_ = 1;
v___x_1911_ = l_Lean_Name_toString(v_fieldName_1889_, v___x_1910_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 3);
lean_ctor_set(v___x_1902_, 0, v___x_1911_);
v___x_1913_ = v___x_1902_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1909_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_a_1900_);
v___x_1918_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v_a_1905_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1890_, v_stx_1891_);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1924_);
v___x_1926_ = v___x_1907_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_del_object(v___x_1902_);
lean_dec(v_a_1900_);
lean_dec_ref(v_ctx_1890_);
lean_dec(v_fieldName_1889_);
return v___x_1904_;
}
}
}
else
{
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v_ctx_1890_);
lean_dec(v_fieldName_1889_);
lean_dec_ref(v_val_1888_);
return v___x_1899_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v_ctx_1890_);
lean_dec(v_fieldName_1889_);
lean_dec_ref(v_val_1888_);
v_a_1931_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1897_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1897_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1939_, lean_object* v_fieldName_1940_, lean_object* v_ctx_1941_, lean_object* v_stx_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1939_, v_fieldName_1940_, v_ctx_1941_, v_stx_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v_stx_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1949_, lean_object* v_info_1950_){
_start:
{
lean_object* v_fieldName_1952_; lean_object* v_lctx_1953_; lean_object* v_val_1954_; lean_object* v_stx_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; 
v_fieldName_1952_ = lean_ctor_get(v_info_1950_, 1);
lean_inc(v_fieldName_1952_);
v_lctx_1953_ = lean_ctor_get(v_info_1950_, 2);
lean_inc_ref(v_lctx_1953_);
v_val_1954_ = lean_ctor_get(v_info_1950_, 3);
lean_inc_ref(v_val_1954_);
v_stx_1955_ = lean_ctor_get(v_info_1950_, 4);
lean_inc(v_stx_1955_);
lean_dec_ref(v_info_1950_);
lean_inc_ref(v_ctx_1949_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1956_, 0, v_val_1954_);
lean_closure_set(v___f_1956_, 1, v_fieldName_1952_);
lean_closure_set(v___f_1956_, 2, v_ctx_1949_);
lean_closure_set(v___f_1956_, 3, v_stx_1955_);
v___x_1957_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1949_, v_lctx_1953_, v___f_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1958_, lean_object* v_info_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Elab_FieldInfo_format(v_ctx_1958_, v_info_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 0)
{
lean_dec(v_pre_1962_);
return v_x_1963_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1975_; 
v_head_1965_ = lean_ctor_get(v_x_1964_, 0);
v_tail_1966_ = lean_ctor_get(v_x_1964_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_x_1964_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1968_ = v_x_1964_;
v_isShared_1969_ = v_isSharedCheck_1975_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_tail_1966_);
lean_inc(v_head_1965_);
lean_dec(v_x_1964_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1975_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
lean_inc(v_pre_1962_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 5);
lean_ctor_set(v___x_1968_, 1, v_pre_1962_);
lean_ctor_set(v___x_1968_, 0, v_x_1963_);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_x_1963_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_pre_1962_);
v___x_1971_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v_head_1965_);
v_x_1963_ = v___x_1972_;
v_x_1964_ = v_tail_1966_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1976_, lean_object* v_x_1977_){
_start:
{
if (lean_obj_tag(v_x_1977_) == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_pre_1976_);
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
lean_object* v_head_1979_; lean_object* v_tail_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_head_1979_ = lean_ctor_get(v_x_1977_, 0);
v_tail_1980_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v_x_1977_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_tail_1980_);
lean_inc(v_head_1979_);
lean_dec(v_x_1977_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
lean_inc(v_pre_1976_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 5);
lean_ctor_set(v___x_1982_, 1, v_head_1979_);
lean_ctor_set(v___x_1982_, 0, v_pre_1976_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_pre_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_head_1979_);
v___x_1985_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1976_, v___x_1985_, v_tail_1980_);
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = l_List_reverse___redArg(v_x_1990_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
return v___x_1997_;
}
else
{
lean_object* v_head_1998_; lean_object* v_tail_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2017_; 
v_head_1998_ = lean_ctor_get(v_x_1989_, 0);
v_tail_1999_ = lean_ctor_get(v_x_1989_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_1989_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2001_ = v_x_1989_;
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_tail_1999_);
lean_inc(v_head_1998_);
lean_dec(v_x_1989_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Meta_ppGoal(v_head_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v_head_1998_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2003_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v_x_1990_);
lean_ctor_set(v___x_2001_, 0, v_a_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2004_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_x_1990_);
v___x_2006_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
v_x_1989_ = v_tail_1999_;
v_x_1990_ = v___x_2006_;
goto _start;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_2001_);
lean_dec(v_tail_1999_);
lean_dec(v_x_1990_);
v_a_2009_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2003_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2003_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_2018_, v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_2029_, lean_object* v___x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_2029_, v___x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2046_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2042_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2041_, v_a_2037_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2036_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2036_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_2055_, lean_object* v___x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_2055_, v___x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2062_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_unsigned_to_nat(32u);
v___x_2067_ = lean_mk_empty_array_with_capacity(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2069_ = ((size_t)5ULL);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_unsigned_to_nat(32u);
v___x_2072_ = lean_mk_empty_array_with_capacity(v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2074_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v___x_2072_);
lean_ctor_set(v___x_2074_, 2, v___x_2070_);
lean_ctor_set(v___x_2074_, 3, v___x_2070_);
lean_ctor_set_usize(v___x_2074_, 4, v___x_2069_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_box(1);
v___x_2076_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2077_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_2078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_2082_, lean_object* v_goals_2083_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = l_List_isEmpty___redArg(v_goals_2083_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; 
v___x_2086_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_2087_ = lean_box(0);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2088_, 0, v_goals_2083_);
lean_closure_set(v___f_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_2082_, v___x_2086_, v___f_2088_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec(v_goals_2083_);
lean_dec_ref(v_ctx_2082_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_2092_, lean_object* v_goals_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_2092_, v_goals_2093_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_2105_, lean_object* v_info_2106_){
_start:
{
lean_object* v_toCommandContextInfo_2108_; lean_object* v_parentDecl_x3f_2109_; lean_object* v_autoImplicits_2110_; lean_object* v_env_2111_; lean_object* v_cmdEnv_x3f_2112_; lean_object* v_fileMap_2113_; lean_object* v_options_2114_; lean_object* v_currNamespace_2115_; lean_object* v_openDecls_2116_; lean_object* v_ngen_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2159_; 
v_toCommandContextInfo_2108_ = lean_ctor_get(v_ctx_2105_, 0);
lean_inc_ref(v_toCommandContextInfo_2108_);
v_parentDecl_x3f_2109_ = lean_ctor_get(v_ctx_2105_, 1);
v_autoImplicits_2110_ = lean_ctor_get(v_ctx_2105_, 2);
v_env_2111_ = lean_ctor_get(v_toCommandContextInfo_2108_, 0);
v_cmdEnv_x3f_2112_ = lean_ctor_get(v_toCommandContextInfo_2108_, 1);
v_fileMap_2113_ = lean_ctor_get(v_toCommandContextInfo_2108_, 2);
v_options_2114_ = lean_ctor_get(v_toCommandContextInfo_2108_, 4);
v_currNamespace_2115_ = lean_ctor_get(v_toCommandContextInfo_2108_, 5);
v_openDecls_2116_ = lean_ctor_get(v_toCommandContextInfo_2108_, 6);
v_ngen_2117_ = lean_ctor_get(v_toCommandContextInfo_2108_, 7);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_toCommandContextInfo_2108_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_toCommandContextInfo_2108_, 3);
lean_dec(v_unused_2160_);
v___x_2119_ = v_toCommandContextInfo_2108_;
v_isShared_2120_ = v_isSharedCheck_2159_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_ngen_2117_);
lean_inc(v_openDecls_2116_);
lean_inc(v_currNamespace_2115_);
lean_inc(v_options_2114_);
lean_inc(v_fileMap_2113_);
lean_inc(v_cmdEnv_x3f_2112_);
lean_inc(v_env_2111_);
lean_dec(v_toCommandContextInfo_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2159_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_toElabInfo_2121_; lean_object* v_mctxBefore_2122_; lean_object* v_goalsBefore_2123_; lean_object* v_mctxAfter_2124_; lean_object* v_goalsAfter_2125_; lean_object* v___x_2127_; 
v_toElabInfo_2121_ = lean_ctor_get(v_info_2106_, 0);
lean_inc_ref(v_toElabInfo_2121_);
v_mctxBefore_2122_ = lean_ctor_get(v_info_2106_, 1);
lean_inc_ref(v_mctxBefore_2122_);
v_goalsBefore_2123_ = lean_ctor_get(v_info_2106_, 2);
lean_inc(v_goalsBefore_2123_);
v_mctxAfter_2124_ = lean_ctor_get(v_info_2106_, 3);
lean_inc_ref(v_mctxAfter_2124_);
v_goalsAfter_2125_ = lean_ctor_get(v_info_2106_, 4);
lean_inc(v_goalsAfter_2125_);
lean_dec_ref(v_info_2106_);
lean_inc_ref(v_ngen_2117_);
lean_inc(v_openDecls_2116_);
lean_inc(v_currNamespace_2115_);
lean_inc_ref(v_options_2114_);
lean_inc_ref(v_fileMap_2113_);
lean_inc(v_cmdEnv_x3f_2112_);
lean_inc_ref(v_env_2111_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 3, v_mctxBefore_2122_);
v___x_2127_ = v___x_2119_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_env_2111_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_cmdEnv_x3f_2112_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_fileMap_2113_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_mctxBefore_2122_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_options_2114_);
lean_ctor_set(v_reuseFailAlloc_2158_, 5, v_currNamespace_2115_);
lean_ctor_set(v_reuseFailAlloc_2158_, 6, v_openDecls_2116_);
lean_ctor_set(v_reuseFailAlloc_2158_, 7, v_ngen_2117_);
v___x_2127_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v_ctxB_2128_; lean_object* v___x_2129_; 
lean_inc_ref(v_autoImplicits_2110_);
lean_inc(v_parentDecl_x3f_2109_);
v_ctxB_2128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_2128_, 0, v___x_2127_);
lean_ctor_set(v_ctxB_2128_, 1, v_parentDecl_x3f_2109_);
lean_ctor_set(v_ctxB_2128_, 2, v_autoImplicits_2110_);
v___x_2129_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_2128_, v_goalsBefore_2123_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v_ctxA_2132_; lean_object* v___x_2133_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2131_, 0, v_env_2111_);
lean_ctor_set(v___x_2131_, 1, v_cmdEnv_x3f_2112_);
lean_ctor_set(v___x_2131_, 2, v_fileMap_2113_);
lean_ctor_set(v___x_2131_, 3, v_mctxAfter_2124_);
lean_ctor_set(v___x_2131_, 4, v_options_2114_);
lean_ctor_set(v___x_2131_, 5, v_currNamespace_2115_);
lean_ctor_set(v___x_2131_, 6, v_openDecls_2116_);
lean_ctor_set(v___x_2131_, 7, v_ngen_2117_);
lean_inc_ref(v_autoImplicits_2110_);
lean_inc(v_parentDecl_x3f_2109_);
v_ctxA_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_2132_, 0, v___x_2131_);
lean_ctor_set(v_ctxA_2132_, 1, v_parentDecl_x3f_2109_);
lean_ctor_set(v_ctxA_2132_, 2, v_autoImplicits_2110_);
v___x_2133_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_2132_, v_goalsAfter_2125_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2157_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2157_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2157_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_stx_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v_stx_2138_ = lean_ctor_get(v_toElabInfo_2121_, 1);
lean_inc(v_stx_2138_);
v___x_2139_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_2140_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2105_, v_toElabInfo_2121_);
v___x_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_box(0);
v___x_2145_ = 0;
v___x_2146_ = l_Lean_Syntax_formatStx(v_stx_2138_, v___x_2144_, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2143_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v_a_2130_);
v___x_2151_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_a_2134_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2153_);
v___x_2155_ = v___x_2136_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
else
{
lean_dec(v_a_2130_);
lean_dec_ref(v_toElabInfo_2121_);
lean_dec_ref(v_ctx_2105_);
return v___x_2133_;
}
}
else
{
lean_dec(v_goalsAfter_2125_);
lean_dec_ref(v_mctxAfter_2124_);
lean_dec_ref(v_toElabInfo_2121_);
lean_dec_ref(v_ngen_2117_);
lean_dec(v_openDecls_2116_);
lean_dec(v_currNamespace_2115_);
lean_dec_ref(v_options_2114_);
lean_dec_ref(v_fileMap_2113_);
lean_dec(v_cmdEnv_x3f_2112_);
lean_dec_ref(v_env_2111_);
lean_dec_ref(v_ctx_2105_);
return v___x_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_2161_, lean_object* v_info_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Elab_TacticInfo_format(v_ctx_2161_, v_info_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_2171_, lean_object* v_info_2172_){
_start:
{
lean_object* v_lctx_2174_; lean_object* v_stx_2175_; lean_object* v_output_2176_; lean_object* v___x_2177_; lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2192_; 
v_lctx_2174_ = lean_ctor_get(v_info_2172_, 0);
lean_inc_ref_n(v_lctx_2174_, 2);
v_stx_2175_ = lean_ctor_get(v_info_2172_, 1);
lean_inc(v_stx_2175_);
v_output_2176_ = lean_ctor_get(v_info_2172_, 2);
lean_inc(v_output_2176_);
lean_dec_ref(v_info_2172_);
v___x_2177_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2171_, v_lctx_2174_, v_stx_2175_);
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v___x_2179_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2171_, v_lctx_2174_, v_output_2176_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2192_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2192_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2184_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v_a_2178_);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2188_);
v___x_2190_ = v___x_2182_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_2193_, lean_object* v_info_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2193_, v_info_2194_);
lean_dec_ref(v_ctx_2193_);
return v_res_2196_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = 1;
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_2203_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
lean_ctor_set_usize(v___x_2203_, 2, v___x_2201_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*3, v___x_2200_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_2207_){
_start:
{
lean_object* v_toWidgetInstance_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2237_; 
v_toWidgetInstance_2208_ = lean_ctor_get(v_info_2207_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_info_2207_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v_info_2207_, 1);
lean_dec(v_unused_2238_);
v___x_2210_ = v_info_2207_;
v_isShared_2211_ = v_isSharedCheck_2237_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_toWidgetInstance_2208_);
lean_dec(v_info_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2237_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_id_2212_; lean_object* v_props_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_fst_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2235_; 
v_id_2212_ = lean_ctor_get(v_toWidgetInstance_2208_, 0);
lean_inc(v_id_2212_);
v_props_2213_ = lean_ctor_get(v_toWidgetInstance_2208_, 1);
lean_inc_ref(v_props_2213_);
lean_dec_ref(v_toWidgetInstance_2208_);
v___x_2214_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_2215_ = lean_apply_1(v_props_2213_, v___x_2214_);
v_fst_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v___x_2215_, 1);
lean_dec(v_unused_2236_);
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2235_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_fst_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2235_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2220_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_2221_ = 1;
v___x_2222_ = l_Lean_Name_toString(v_id_2212_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 5);
lean_ctor_set(v___x_2218_, 1, v___x_2223_);
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2225_ = v___x_2218_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 5);
lean_ctor_set(v___x_2210_, 1, v___x_2226_);
lean_ctor_set(v___x_2210_, 0, v___x_2225_);
v___x_2228_ = v___x_2210_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_unsigned_to_nat(80u);
v___x_2230_ = l_Lean_Json_pretty(v_fst_2216_, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2228_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
return v___x_2232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_2245_){
_start:
{
lean_object* v_userName_2246_; lean_object* v_id_2247_; lean_object* v_baseId_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_userName_2246_ = lean_ctor_get(v_info_2245_, 0);
lean_inc(v_userName_2246_);
v_id_2247_ = lean_ctor_get(v_info_2245_, 1);
lean_inc(v_id_2247_);
v_baseId_2248_ = lean_ctor_get(v_info_2245_, 2);
lean_inc(v_baseId_2248_);
lean_dec_ref(v_info_2245_);
v___x_2249_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_2250_ = lean_erase_macro_scopes(v_userName_2246_);
v___x_2251_ = 1;
v___x_2252_ = l_Lean_Name_toString(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2249_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_Name_toString(v_id_2247_, v___x_2251_);
v___x_2258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_Name_toString(v_baseId_2248_, v___x_2251_);
v___x_2263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2261_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_2268_, lean_object* v_info_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_2271_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_2268_, v_info_2269_);
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_2273_, lean_object* v_info_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2273_, v_info_2274_);
lean_dec(v_info_2274_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_2278_, lean_object* v_info_2279_){
_start:
{
lean_object* v_mkDocString_x3f_2281_; 
v_mkDocString_x3f_2281_ = lean_ctor_get(v_info_2279_, 2);
lean_inc(v_mkDocString_x3f_2281_);
lean_dec_ref(v_info_2279_);
if (lean_obj_tag(v_mkDocString_x3f_2281_) == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_ppCtx_2278_);
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2316_; 
v_val_2284_ = lean_ctor_get(v_mkDocString_x3f_2281_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_mkDocString_x3f_2281_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2286_ = v_mkDocString_x3f_2281_;
v_isShared_2287_ = v_isSharedCheck_2316_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v_mkDocString_x3f_2281_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2316_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_apply_2(v_val_2284_, v_ppCtx_2278_, lean_box(0));
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2299_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2299_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2299_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_a_2289_);
v___x_2294_ = v___x_2286_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2296_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2315_; 
v_a_2300_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2302_ = v___x_2288_;
v_isShared_2303_ = v_isSharedCheck_2315_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2288_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2315_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2304_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_2305_ = lean_io_error_to_string(v_a_2300_);
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2308_);
v___x_2310_ = v___x_2286_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set_tag(v___x_2302_, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2310_);
v___x_2312_ = v___x_2302_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_2317_, lean_object* v_info_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_2317_, v_info_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2321_, lean_object* v_x_2322_){
_start:
{
if (lean_obj_tag(v_x_2321_) == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2323_;
}
else
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2335_; 
v_val_2324_ = lean_ctor_get(v_x_2321_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_x_2321_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2326_ = v_x_2321_;
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_x_2321_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2329_ = l_String_quote(v_val_2324_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 3);
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Repr_addAppParen(v___x_2332_, v_x_2322_);
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2336_, v_x_2337_);
lean_dec(v_x_2337_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2353_, lean_object* v_info_2354_){
_start:
{
lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v_toTermInfo_2362_; lean_object* v_location_x3f_2363_; uint8_t v_explicit_2364_; lean_object* v___y_2366_; 
v_toTermInfo_2362_ = lean_ctor_get(v_info_2354_, 0);
lean_inc_ref(v_toTermInfo_2362_);
v_location_x3f_2363_ = lean_ctor_get(v_info_2354_, 1);
lean_inc(v_location_x3f_2363_);
v_explicit_2364_ = lean_ctor_get_uint8(v_info_2354_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_2363_) == 1)
{
lean_object* v_val_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2448_; 
v_val_2387_ = lean_ctor_get(v_location_x3f_2363_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_location_x3f_2363_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2389_ = v_location_x3f_2363_;
v_isShared_2390_ = v_isSharedCheck_2448_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_val_2387_);
lean_dec(v_location_x3f_2363_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2448_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_range_2391_; lean_object* v_pos_2392_; lean_object* v_endPos_2393_; lean_object* v_module_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2446_; 
v_range_2391_ = lean_ctor_get(v_val_2387_, 1);
v_pos_2392_ = lean_ctor_get(v_range_2391_, 0);
lean_inc_ref(v_pos_2392_);
v_endPos_2393_ = lean_ctor_get(v_range_2391_, 2);
lean_inc_ref(v_endPos_2393_);
v_module_2394_ = lean_ctor_get(v_val_2387_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_val_2387_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; 
v_unused_2447_ = lean_ctor_get(v_val_2387_, 1);
lean_dec(v_unused_2447_);
v___x_2396_ = v_val_2387_;
v_isShared_2397_ = v_isSharedCheck_2446_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_module_2394_);
lean_dec(v_val_2387_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2446_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_line_2398_; lean_object* v_column_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2445_; 
v_line_2398_ = lean_ctor_get(v_pos_2392_, 0);
v_column_2399_ = lean_ctor_get(v_pos_2392_, 1);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_pos_2392_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2401_ = v_pos_2392_;
v_isShared_2402_ = v_isSharedCheck_2445_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_column_2399_);
lean_inc(v_line_2398_);
lean_dec(v_pos_2392_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2445_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v_line_2403_; lean_object* v_column_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2444_; 
v_line_2403_ = lean_ctor_get(v_endPos_2393_, 0);
v_column_2404_ = lean_ctor_get(v_endPos_2393_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_endPos_2393_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2406_ = v_endPos_2393_;
v_isShared_2407_ = v_isSharedCheck_2444_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_column_2404_);
lean_inc(v_line_2403_);
lean_dec(v_endPos_2393_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2444_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = 1;
v___x_2409_ = l_Lean_Name_toString(v_module_2394_, v___x_2408_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 3);
lean_ctor_set(v___x_2389_, 0, v___x_2409_);
v___x_2411_ = v___x_2389_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 5);
lean_ctor_set(v___x_2406_, 1, v___x_2412_);
lean_ctor_set(v___x_2406_, 0, v___x_2411_);
v___x_2414_ = v___x_2406_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2416_ = l_Nat_reprFast(v_line_2398_);
v___x_2417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 5);
lean_ctor_set(v___x_2401_, 1, v___x_2417_);
lean_ctor_set(v___x_2401_, 0, v___x_2415_);
v___x_2419_ = v___x_2401_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 5);
lean_ctor_set(v___x_2396_, 1, v___x_2420_);
lean_ctor_set(v___x_2396_, 0, v___x_2419_);
v___x_2422_ = v___x_2396_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2423_ = l_Nat_reprFast(v_column_2399_);
v___x_2424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2422_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2414_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_Nat_reprFast(v_line_2403_);
v___x_2432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2415_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2420_);
v___x_2435_ = l_Nat_reprFast(v_column_2404_);
v___x_2436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2434_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2426_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2430_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___y_2366_ = v___x_2439_;
goto v___jp_2365_;
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
lean_object* v___x_2449_; 
lean_dec(v_location_x3f_2363_);
v___x_2449_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2366_ = v___x_2449_;
goto v___jp_2365_;
}
v___jp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_inc_ref(v___y_2358_);
v___x_2359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___y_2358_);
v___x_2360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___y_2357_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
v___jp_2365_:
{
lean_object* v_lctx_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_lctx_2367_ = lean_ctor_get(v_toTermInfo_2362_, 1);
lean_inc_ref(v_lctx_2367_);
v___x_2368_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_2353_, v_lctx_2367_);
v___x_2369_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_2368_, v_info_2354_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = l_Lean_Elab_TermInfo_format(v_ctx_2353_, v_toTermInfo_2362_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_a_2372_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___y_2366_);
v___x_2378_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_2370_, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
if (v_explicit_2364_ == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2357_ = v___x_2384_;
v___y_2358_ = v___x_2385_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2357_ = v___x_2384_;
v___y_2358_ = v___x_2386_;
goto v___jp_2356_;
}
}
else
{
lean_dec(v_a_2370_);
lean_dec(v___y_2366_);
return v___x_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2450_, lean_object* v_info_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2450_, v_info_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2457_, lean_object* v_info_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2460_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2457_, v_info_2458_);
v___x_2461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2465_, lean_object* v_info_2466_){
_start:
{
lean_object* v_stx_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_stx_2467_ = lean_ctor_get(v_info_2466_, 1);
v___x_2468_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2467_);
v___x_2469_ = l_Lean_Syntax_getKind(v_stx_2467_);
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Name_toString(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2468_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2465_, v_info_2466_);
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2487_, lean_object* v_info_2488_){
_start:
{
lean_object* v_toElabInfo_2489_; lean_object* v_name_2490_; uint8_t v_kind_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_toElabInfo_2489_ = lean_ctor_get(v_info_2488_, 0);
lean_inc_ref(v_toElabInfo_2489_);
v_name_2490_ = lean_ctor_get(v_info_2488_, 1);
lean_inc(v_name_2490_);
v_kind_2491_ = lean_ctor_get_uint8(v_info_2488_, sizeof(void*)*2);
lean_dec_ref(v_info_2488_);
v___x_2492_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2493_ = 1;
v___x_2494_ = l_Lean_Name_toString(v_name_2490_, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2492_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_unsigned_to_nat(0u);
v___x_2500_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2491_, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2487_, v_toElabInfo_2489_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2506_, lean_object* v_x_2507_){
_start:
{
switch(lean_obj_tag(v_x_2507_))
{
case 0:
{
lean_object* v_i_2509_; lean_object* v___x_2510_; 
v_i_2509_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2509_);
lean_dec_ref(v_x_2507_);
v___x_2510_ = l_Lean_Elab_TacticInfo_format(v_ctx_2506_, v_i_2509_);
return v___x_2510_;
}
case 1:
{
lean_object* v_i_2511_; lean_object* v___x_2512_; 
v_i_2511_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2511_);
lean_dec_ref(v_x_2507_);
v___x_2512_ = l_Lean_Elab_TermInfo_format(v_ctx_2506_, v_i_2511_);
return v___x_2512_;
}
case 2:
{
lean_object* v_i_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2521_; 
v_i_2513_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2515_ = v_x_2507_;
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_i_2513_);
lean_dec(v_x_2507_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2506_, v_i_2513_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2517_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
case 3:
{
lean_object* v_i_2522_; lean_object* v___x_2523_; 
v_i_2522_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2522_);
lean_dec_ref(v_x_2507_);
v___x_2523_ = l_Lean_Elab_CommandInfo_format(v_ctx_2506_, v_i_2522_);
return v___x_2523_;
}
case 4:
{
lean_object* v_i_2524_; lean_object* v___x_2525_; 
v_i_2524_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2524_);
lean_dec_ref(v_x_2507_);
v___x_2525_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2506_, v_i_2524_);
lean_dec_ref(v_ctx_2506_);
return v___x_2525_;
}
case 5:
{
lean_object* v_i_2526_; lean_object* v___x_2527_; 
v_i_2526_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2526_);
lean_dec_ref(v_x_2507_);
v___x_2527_ = l_Lean_Elab_OptionInfo_format(v_ctx_2506_, v_i_2526_);
return v___x_2527_;
}
case 6:
{
lean_object* v_i_2528_; lean_object* v___x_2529_; 
v_i_2528_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2528_);
lean_dec_ref(v_x_2507_);
v___x_2529_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2506_, v_i_2528_);
return v___x_2529_;
}
case 7:
{
lean_object* v_i_2530_; lean_object* v___x_2531_; 
v_i_2530_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2530_);
lean_dec_ref(v_x_2507_);
v___x_2531_ = l_Lean_Elab_FieldInfo_format(v_ctx_2506_, v_i_2530_);
return v___x_2531_;
}
case 8:
{
lean_object* v_i_2532_; lean_object* v___x_2533_; 
v_i_2532_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2532_);
lean_dec_ref(v_x_2507_);
v___x_2533_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2506_, v_i_2532_);
return v___x_2533_;
}
case 9:
{
lean_object* v_i_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_ctx_2506_);
v_i_2534_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v_x_2507_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_i_2534_);
lean_dec(v_x_2507_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
case 10:
{
lean_object* v_i_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_ctx_2506_);
v_i_2543_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v_x_2507_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_i_2543_);
lean_dec(v_x_2507_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = l_Lean_Elab_CustomInfo_format(v_i_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
case 11:
{
lean_object* v_i_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_ctx_2506_);
v_i_2552_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2554_ = v_x_2507_;
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_i_2552_);
lean_dec(v_x_2507_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
case 12:
{
lean_object* v_i_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
v_i_2561_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2563_ = v_x_2507_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_i_2561_);
lean_dec(v_x_2507_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2506_, v_i_2561_);
lean_dec(v_i_2561_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
case 13:
{
lean_object* v_i_2570_; lean_object* v___x_2571_; 
v_i_2570_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_i_2570_);
lean_dec_ref(v_x_2507_);
v___x_2571_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2506_, v_i_2570_);
return v___x_2571_;
}
case 14:
{
lean_object* v_i_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2580_; 
v_i_2572_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2574_ = v_x_2507_;
v_isShared_2575_ = v_isSharedCheck_2580_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_i_2572_);
lean_dec(v_x_2507_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2580_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2506_, v_i_2572_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2576_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
case 15:
{
lean_object* v_i_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2589_; 
v_i_2581_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2583_ = v_x_2507_;
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_i_2581_);
lean_dec(v_x_2507_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = l_Lean_Elab_DocInfo_format(v_ctx_2506_, v_i_2581_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2585_);
v___x_2587_ = v___x_2583_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
default: 
{
lean_object* v_i_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2598_; 
v_i_2590_ = lean_ctor_get(v_x_2507_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_x_2507_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2592_ = v_x_2507_;
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_i_2590_);
lean_dec(v_x_2507_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2506_, v_i_2590_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2594_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2599_, lean_object* v_x_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Elab_Info_format(v_ctx_2599_, v_x_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2603_){
_start:
{
switch(lean_obj_tag(v_x_2603_))
{
case 0:
{
lean_object* v_i_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
v_i_2604_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v_x_2603_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_i_2604_);
lean_dec(v_x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_toElabInfo_2608_; lean_object* v___x_2610_; 
v_toElabInfo_2608_ = lean_ctor_get(v_i_2604_, 0);
lean_inc_ref(v_toElabInfo_2608_);
lean_dec_ref(v_i_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 0, v_toElabInfo_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_toElabInfo_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
case 1:
{
lean_object* v_i_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2621_; 
v_i_2613_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2615_ = v_x_2603_;
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_i_2613_);
lean_dec(v_x_2603_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v_toElabInfo_2617_; lean_object* v___x_2619_; 
v_toElabInfo_2617_ = lean_ctor_get(v_i_2613_, 0);
lean_inc_ref(v_toElabInfo_2617_);
lean_dec_ref(v_i_2613_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_toElabInfo_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_toElabInfo_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
case 2:
{
lean_object* v_i_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2630_; 
v_i_2622_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2624_ = v_x_2603_;
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_i_2622_);
lean_dec(v_x_2603_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_toElabInfo_2626_; lean_object* v___x_2628_; 
v_toElabInfo_2626_ = lean_ctor_get(v_i_2622_, 0);
lean_inc_ref(v_toElabInfo_2626_);
lean_dec_ref(v_i_2622_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v_toElabInfo_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_toElabInfo_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
case 3:
{
lean_object* v_i_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_i_2631_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v_x_2603_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_i_2631_);
lean_dec(v_x_2603_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set_tag(v___x_2633_, 1);
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_i_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
case 13:
{
lean_object* v_i_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2648_; 
v_i_2639_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2641_ = v_x_2603_;
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_i_2639_);
lean_dec(v_x_2603_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_toTermInfo_2643_; lean_object* v_toElabInfo_2644_; lean_object* v___x_2646_; 
v_toTermInfo_2643_ = lean_ctor_get(v_i_2639_, 0);
lean_inc_ref(v_toTermInfo_2643_);
lean_dec_ref(v_i_2639_);
v_toElabInfo_2644_ = lean_ctor_get(v_toTermInfo_2643_, 0);
lean_inc_ref(v_toElabInfo_2644_);
lean_dec_ref(v_toTermInfo_2643_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v_toElabInfo_2644_);
v___x_2646_ = v___x_2641_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_toElabInfo_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
case 14:
{
lean_object* v_i_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_i_2649_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v_x_2603_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_i_2649_);
lean_dec(v_x_2603_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_i_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
case 15:
{
lean_object* v_i_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_i_2657_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v_x_2603_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_i_2657_);
lean_dec(v_x_2603_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 1);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_i_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
case 16:
{
lean_object* v_i_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2673_; 
v_i_2665_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2667_ = v_x_2603_;
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_i_2665_);
lean_dec(v_x_2603_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_toElabInfo_2669_; lean_object* v___x_2671_; 
v_toElabInfo_2669_ = lean_ctor_get(v_i_2665_, 0);
lean_inc_ref(v_toElabInfo_2669_);
lean_dec_ref(v_i_2665_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 1);
lean_ctor_set(v___x_2667_, 0, v_toElabInfo_2669_);
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_toElabInfo_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
default: 
{
lean_object* v___x_2674_; 
lean_dec_ref(v_x_2603_);
v___x_2674_ = lean_box(0);
return v___x_2674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
if (lean_obj_tag(v_x_2675_) == 1)
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v_val_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2712_; 
v_val_2677_ = lean_ctor_get(v_x_2675_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_x_2675_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2679_ = v_x_2675_;
v_isShared_2680_ = v_isSharedCheck_2712_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_val_2677_);
lean_dec(v_x_2675_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2712_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_toCommandContextInfo_2681_; lean_object* v_i_2682_; lean_object* v_parentDecl_x3f_2683_; lean_object* v_autoImplicits_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2710_; 
v_toCommandContextInfo_2681_ = lean_ctor_get(v_val_2677_, 0);
lean_inc_ref(v_toCommandContextInfo_2681_);
v_i_2682_ = lean_ctor_get(v_x_2676_, 0);
v_parentDecl_x3f_2683_ = lean_ctor_get(v_val_2677_, 1);
v_autoImplicits_2684_ = lean_ctor_get(v_val_2677_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_val_2677_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v_val_2677_, 0);
lean_dec(v_unused_2711_);
v___x_2686_ = v_val_2677_;
v_isShared_2687_ = v_isSharedCheck_2710_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_autoImplicits_2684_);
lean_inc(v_parentDecl_x3f_2683_);
lean_dec(v_val_2677_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2710_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_env_2688_; lean_object* v_cmdEnv_x3f_2689_; lean_object* v_fileMap_2690_; lean_object* v_options_2691_; lean_object* v_currNamespace_2692_; lean_object* v_openDecls_2693_; lean_object* v_ngen_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2708_; 
v_env_2688_ = lean_ctor_get(v_toCommandContextInfo_2681_, 0);
v_cmdEnv_x3f_2689_ = lean_ctor_get(v_toCommandContextInfo_2681_, 1);
v_fileMap_2690_ = lean_ctor_get(v_toCommandContextInfo_2681_, 2);
v_options_2691_ = lean_ctor_get(v_toCommandContextInfo_2681_, 4);
v_currNamespace_2692_ = lean_ctor_get(v_toCommandContextInfo_2681_, 5);
v_openDecls_2693_ = lean_ctor_get(v_toCommandContextInfo_2681_, 6);
v_ngen_2694_ = lean_ctor_get(v_toCommandContextInfo_2681_, 7);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_toCommandContextInfo_2681_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_toCommandContextInfo_2681_, 3);
lean_dec(v_unused_2709_);
v___x_2696_ = v_toCommandContextInfo_2681_;
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_ngen_2694_);
lean_inc(v_openDecls_2693_);
lean_inc(v_currNamespace_2692_);
lean_inc(v_options_2691_);
lean_inc(v_fileMap_2690_);
lean_inc(v_cmdEnv_x3f_2689_);
lean_inc(v_env_2688_);
lean_dec(v_toCommandContextInfo_2681_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_mctxAfter_2698_; lean_object* v___x_2700_; 
v_mctxAfter_2698_ = lean_ctor_get(v_i_2682_, 3);
lean_inc_ref(v_mctxAfter_2698_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 3, v_mctxAfter_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_env_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_cmdEnv_x3f_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_fileMap_2690_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_mctxAfter_2698_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_options_2691_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_currNamespace_2692_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_openDecls_2693_);
lean_ctor_set(v_reuseFailAlloc_2707_, 7, v_ngen_2694_);
v___x_2700_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2700_);
v___x_2702_ = v___x_2686_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_parentDecl_x3f_2683_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_autoImplicits_2684_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2702_);
v___x_2704_ = v___x_2679_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
}
else
{
return v_x_2675_;
}
}
else
{
return v_x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2713_, v_x_2714_);
lean_dec_ref(v_x_2714_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
if (lean_obj_tag(v_x_2717_) == 0)
{
return v_x_2716_;
}
else
{
lean_object* v_head_2718_; lean_object* v_tail_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_head_2718_ = lean_ctor_get(v_x_2717_, 0);
v_tail_2719_ = lean_ctor_get(v_x_2717_, 1);
v___x_2720_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2721_ = lean_string_append(v_x_2716_, v___x_2720_);
v___x_2722_ = lean_expr_dbg_to_string(v_head_2718_);
v___x_2723_ = lean_string_append(v___x_2721_, v___x_2722_);
lean_dec_ref(v___x_2722_);
v_x_2716_ = v___x_2723_;
v_x_2717_ = v_tail_2719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2725_, lean_object* v_x_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2725_, v_x_2726_);
lean_dec(v_x_2726_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2730_){
_start:
{
if (lean_obj_tag(v_x_2730_) == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2731_;
}
else
{
lean_object* v_tail_2732_; 
v_tail_2732_ = lean_ctor_get(v_x_2730_, 1);
if (lean_obj_tag(v_tail_2732_) == 0)
{
lean_object* v_head_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_head_2733_ = lean_ctor_get(v_x_2730_, 0);
v___x_2734_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2735_ = lean_expr_dbg_to_string(v_head_2733_);
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2738_ = lean_string_append(v___x_2736_, v___x_2737_);
return v___x_2738_;
}
else
{
lean_object* v_head_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint32_t v___x_2744_; lean_object* v___x_2745_; 
v_head_2739_ = lean_ctor_get(v_x_2730_, 0);
v___x_2740_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2741_ = lean_expr_dbg_to_string(v_head_2739_);
v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2742_, v_tail_2732_);
v___x_2744_ = 93;
v___x_2745_ = lean_string_push(v___x_2743_, v___x_2744_);
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2746_);
lean_dec(v_x_2746_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2754_){
_start:
{
switch(lean_obj_tag(v_ctx_2754_))
{
case 0:
{
lean_object* v___x_2755_; 
lean_dec_ref(v_ctx_2754_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2755_;
}
case 1:
{
lean_object* v_parentDecl_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2769_; 
v_parentDecl_2756_ = lean_ctor_get(v_ctx_2754_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_ctx_2754_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2758_ = v_ctx_2754_;
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_parentDecl_2756_);
lean_dec(v_ctx_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2760_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2761_ = 1;
v___x_2762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2756_, v___x_2761_);
v___x_2763_ = lean_string_append(v___x_2760_, v___x_2762_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2765_ = lean_string_append(v___x_2763_, v___x_2764_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 3);
lean_ctor_set(v___x_2758_, 0, v___x_2765_);
v___x_2767_ = v___x_2758_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
default: 
{
lean_object* v_autoImplicits_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2785_; 
v_autoImplicits_2770_ = lean_ctor_get(v_ctx_2754_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_ctx_2754_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2772_ = v_ctx_2754_;
v_isShared_2773_ = v_isSharedCheck_2785_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_autoImplicits_2770_);
lean_dec(v_ctx_2754_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2785_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2774_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2775_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2776_ = lean_array_to_list(v_autoImplicits_2770_);
v___x_2777_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2776_);
lean_dec(v___x_2776_);
v___x_2778_ = lean_string_append(v___x_2775_, v___x_2777_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_string_append(v___x_2774_, v___x_2778_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2781_ = lean_string_append(v___x_2779_, v___x_2780_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 3);
lean_ctor_set(v___x_2772_, 0, v___x_2781_);
v___x_2783_ = v___x_2772_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2795_, lean_object* v_ctx_x3f_2796_){
_start:
{
switch(lean_obj_tag(v_tree_2795_))
{
case 0:
{
lean_object* v_i_2798_; lean_object* v_t_2799_; lean_object* v___x_2800_; 
v_i_2798_ = lean_ctor_get(v_tree_2795_, 0);
lean_inc_ref(v_i_2798_);
v_t_2799_ = lean_ctor_get(v_tree_2795_, 1);
lean_inc_ref(v_t_2799_);
lean_dec_ref(v_tree_2795_);
v___x_2800_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2798_, v_ctx_x3f_2796_);
v_tree_2795_ = v_t_2799_;
v_ctx_x3f_2796_ = v___x_2800_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2796_) == 0)
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
lean_dec_ref(v_tree_2795_);
v___x_2802_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
else
{
lean_object* v_i_2804_; lean_object* v_children_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2855_; 
v_i_2804_ = lean_ctor_get(v_tree_2795_, 0);
v_children_2805_ = lean_ctor_get(v_tree_2795_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_tree_2795_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2807_ = v_tree_2795_;
v_isShared_2808_ = v_isSharedCheck_2855_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_children_2805_);
lean_inc(v_i_2804_);
lean_dec(v_tree_2795_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2855_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_val_2809_; lean_object* v___x_2810_; 
v_val_2809_ = lean_ctor_get(v_ctx_x3f_2796_, 0);
lean_inc_ref(v_i_2804_);
lean_inc(v_val_2809_);
v___x_2810_ = l_Lean_Elab_Info_format(v_val_2809_, v_i_2804_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2854_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2854_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2854_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_size_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_size_2815_ = lean_ctor_get(v_children_2805_, 2);
v___x_2816_ = lean_unsigned_to_nat(0u);
v___x_2817_ = lean_nat_dec_eq(v_size_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_del_object(v___x_2813_);
v___x_2818_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2796_, v_i_2804_);
lean_dec_ref(v_i_2804_);
v___x_2819_ = l_Lean_PersistentArray_toList___redArg(v_children_2805_);
lean_dec_ref(v_children_2805_);
v___x_2820_ = lean_box(0);
v___x_2821_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2818_, v___x_2819_, v___x_2820_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2837_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2837_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2837_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 5);
lean_ctor_set(v___x_2807_, 1, v_a_2811_);
lean_ctor_set(v___x_2807_, 0, v___x_2826_);
v___x_2828_ = v___x_2807_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_a_2811_);
v___x_2828_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2829_ = lean_box(1);
v___x_2830_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2829_, v_a_2822_);
v___x_2831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2828_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Std_Format_nestD(v___x_2831_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2832_);
v___x_2834_ = v___x_2824_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_a_2811_);
lean_del_object(v___x_2807_);
v_a_2838_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2821_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2821_);
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
else
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_dec_ref(v_children_2805_);
lean_dec_ref(v_ctx_x3f_2796_);
lean_dec_ref(v_i_2804_);
v___x_2846_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 5);
lean_ctor_set(v___x_2807_, 1, v_a_2811_);
lean_ctor_set(v___x_2807_, 0, v___x_2846_);
v___x_2848_ = v___x_2807_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2846_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_a_2811_);
v___x_2848_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = l_Std_Format_nestD(v___x_2848_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2849_);
v___x_2851_ = v___x_2813_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
else
{
lean_del_object(v___x_2807_);
lean_dec_ref(v_children_2805_);
lean_dec_ref(v_ctx_x3f_2796_);
lean_dec_ref(v_i_2804_);
return v___x_2810_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_ctx_x3f_2796_);
v_mvarId_2856_ = lean_ctor_get(v_tree_2795_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_tree_2795_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2858_ = v_tree_2795_;
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_mvarId_2856_);
lean_dec(v_tree_2795_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2860_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2861_ = 1;
v___x_2862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2856_, v___x_2861_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 3);
lean_ctor_set(v___x_2858_, 0, v___x_2862_);
v___x_2864_ = v___x_2858_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2860_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Std_Format_nestD(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_dec(v___x_2870_);
v___x_2874_ = l_List_reverse___redArg(v_x_2872_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
else
{
lean_object* v_head_2876_; lean_object* v_tail_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2895_; 
v_head_2876_ = lean_ctor_get(v_x_2871_, 0);
v_tail_2877_ = lean_ctor_get(v_x_2871_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2879_ = v_x_2871_;
v_isShared_2880_ = v_isSharedCheck_2895_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_tail_2877_);
lean_inc(v_head_2876_);
lean_dec(v_x_2871_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2895_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; 
lean_inc(v___x_2870_);
v___x_2881_ = l_Lean_Elab_InfoTree_format(v_head_2876_, v___x_2870_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 1, v_x_2872_);
lean_ctor_set(v___x_2879_, 0, v_a_2882_);
v___x_2884_ = v___x_2879_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2882_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_x_2872_);
v___x_2884_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_x_2871_ = v_tail_2877_;
v_x_2872_ = v___x_2884_;
goto _start;
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_del_object(v___x_2879_);
lean_dec(v_tail_2877_);
lean_dec(v_x_2872_);
lean_dec(v___x_2870_);
v_a_2887_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2881_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2881_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2896_, v_x_2897_, v_x_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2901_, lean_object* v_ctx_x3f_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Elab_InfoTree_format(v_tree_2901_, v_ctx_x3f_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2905_, lean_object* v_s_2906_){
_start:
{
uint8_t v_enabled_2907_; lean_object* v_assignment_2908_; lean_object* v_lazyAssignment_2909_; lean_object* v_trees_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2918_; 
v_enabled_2907_ = lean_ctor_get_uint8(v_s_2906_, sizeof(void*)*3);
v_assignment_2908_ = lean_ctor_get(v_s_2906_, 0);
v_lazyAssignment_2909_ = lean_ctor_get(v_s_2906_, 1);
v_trees_2910_ = lean_ctor_get(v_s_2906_, 2);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_s_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2912_ = v_s_2906_;
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_trees_2910_);
lean_inc(v_lazyAssignment_2909_);
lean_inc(v_assignment_2908_);
lean_dec(v_s_2906_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = lean_apply_1(v_f_2905_, v_trees_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 2, v___x_2914_);
v___x_2916_ = v___x_2912_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_assignment_2908_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_lazyAssignment_2909_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v___x_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_2917_, sizeof(void*)*3, v_enabled_2907_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2919_, lean_object* v_f_2920_){
_start:
{
lean_object* v_modifyInfoState_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; 
v_modifyInfoState_2921_ = lean_ctor_get(v_inst_2919_, 1);
lean_inc(v_modifyInfoState_2921_);
lean_dec_ref(v_inst_2919_);
v___f_2922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2922_, 0, v_f_2920_);
v___x_2923_ = lean_apply_1(v_modifyInfoState_2921_, v___f_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2924_, lean_object* v_inst_2925_, lean_object* v_f_2926_){
_start:
{
lean_object* v_modifyInfoState_2927_; lean_object* v___f_2928_; lean_object* v___x_2929_; 
v_modifyInfoState_2927_ = lean_ctor_get(v_inst_2925_, 1);
lean_inc(v_modifyInfoState_2927_);
lean_dec_ref(v_inst_2925_);
v___f_2928_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2928_, 0, v_f_2926_);
v___x_2929_ = lean_apply_1(v_modifyInfoState_2927_, v___f_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_unsigned_to_nat(32u);
v___x_2931_ = lean_mk_empty_array_with_capacity(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2933_ = ((size_t)5ULL);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_unsigned_to_nat(32u);
v___x_2936_ = lean_mk_empty_array_with_capacity(v___x_2935_);
v___x_2937_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2938_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
lean_ctor_set(v___x_2938_, 2, v___x_2934_);
lean_ctor_set(v___x_2938_, 3, v___x_2934_);
lean_ctor_set_usize(v___x_2938_, 4, v___x_2933_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2939_){
_start:
{
uint8_t v_enabled_2940_; lean_object* v_assignment_2941_; lean_object* v_lazyAssignment_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2950_; 
v_enabled_2940_ = lean_ctor_get_uint8(v_s_2939_, sizeof(void*)*3);
v_assignment_2941_ = lean_ctor_get(v_s_2939_, 0);
v_lazyAssignment_2942_ = lean_ctor_get(v_s_2939_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_s_2939_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_s_2939_, 2);
lean_dec(v_unused_2951_);
v___x_2944_ = v_s_2939_;
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_lazyAssignment_2942_);
lean_inc(v_assignment_2941_);
lean_dec(v_s_2939_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 2, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_assignment_2941_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_lazyAssignment_2942_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v___x_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_2949_, sizeof(void*)*3, v_enabled_2940_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2952_, lean_object* v_trees_2953_, lean_object* v_____r_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_apply_2(v_toPure_2952_, lean_box(0), v_trees_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2956_, lean_object* v_modifyInfoState_2957_, lean_object* v___f_2958_, lean_object* v_toBind_2959_, lean_object* v_____do__lift_2960_){
_start:
{
lean_object* v_trees_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_trees_2961_ = lean_ctor_get(v_____do__lift_2960_, 2);
lean_inc_ref(v_trees_2961_);
lean_dec_ref(v_____do__lift_2960_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2962_, 0, v_toPure_2956_);
lean_closure_set(v___f_2962_, 1, v_trees_2961_);
v___x_2963_ = lean_apply_1(v_modifyInfoState_2957_, v___f_2958_);
v___x_2964_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v___x_2963_, v___f_2962_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2966_, lean_object* v_inst_2967_){
_start:
{
lean_object* v_toApplicative_2968_; lean_object* v_toBind_2969_; lean_object* v_getInfoState_2970_; lean_object* v_modifyInfoState_2971_; lean_object* v_toPure_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; 
v_toApplicative_2968_ = lean_ctor_get(v_inst_2966_, 0);
lean_inc_ref(v_toApplicative_2968_);
v_toBind_2969_ = lean_ctor_get(v_inst_2966_, 1);
lean_inc_n(v_toBind_2969_, 2);
lean_dec_ref(v_inst_2966_);
v_getInfoState_2970_ = lean_ctor_get(v_inst_2967_, 0);
lean_inc(v_getInfoState_2970_);
v_modifyInfoState_2971_ = lean_ctor_get(v_inst_2967_, 1);
lean_inc(v_modifyInfoState_2971_);
lean_dec_ref(v_inst_2967_);
v_toPure_2972_ = lean_ctor_get(v_toApplicative_2968_, 1);
lean_inc(v_toPure_2972_);
lean_dec_ref(v_toApplicative_2968_);
v___f_2973_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2974_, 0, v_toPure_2972_);
lean_closure_set(v___f_2974_, 1, v_modifyInfoState_2971_);
lean_closure_set(v___f_2974_, 2, v___f_2973_);
lean_closure_set(v___f_2974_, 3, v_toBind_2969_);
v___x_2975_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v_getInfoState_2970_, v___f_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2977_, v_inst_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2980_, lean_object* v_s_2981_){
_start:
{
uint8_t v_enabled_2982_; lean_object* v_assignment_2983_; lean_object* v_lazyAssignment_2984_; lean_object* v_trees_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2993_; 
v_enabled_2982_ = lean_ctor_get_uint8(v_s_2981_, sizeof(void*)*3);
v_assignment_2983_ = lean_ctor_get(v_s_2981_, 0);
v_lazyAssignment_2984_ = lean_ctor_get(v_s_2981_, 1);
v_trees_2985_ = lean_ctor_get(v_s_2981_, 2);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_s_2981_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2987_ = v_s_2981_;
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_trees_2985_);
lean_inc(v_lazyAssignment_2984_);
lean_inc(v_assignment_2983_);
lean_dec(v_s_2981_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = l_Lean_PersistentArray_push___redArg(v_trees_2985_, v_t_2980_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 2, v___x_2989_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_assignment_2983_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_lazyAssignment_2984_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v___x_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*3, v_enabled_2982_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2994_, lean_object* v_modifyInfoState_2995_, lean_object* v___f_2996_, lean_object* v_____do__lift_2997_){
_start:
{
uint8_t v_enabled_2998_; 
v_enabled_2998_ = lean_ctor_get_uint8(v_____do__lift_2997_, sizeof(void*)*3);
if (v_enabled_2998_ == 0)
{
lean_object* v_toPure_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec_ref(v___f_2996_);
lean_dec(v_modifyInfoState_2995_);
v_toPure_2999_ = lean_ctor_get(v_toApplicative_2994_, 1);
lean_inc(v_toPure_2999_);
lean_dec_ref(v_toApplicative_2994_);
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_apply_2(v_toPure_2999_, lean_box(0), v___x_3000_);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; 
lean_dec_ref(v_toApplicative_2994_);
v___x_3002_ = lean_apply_1(v_modifyInfoState_2995_, v___f_2996_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_3003_, lean_object* v_modifyInfoState_3004_, lean_object* v___f_3005_, lean_object* v_____do__lift_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_3003_, v_modifyInfoState_3004_, v___f_3005_, v_____do__lift_3006_);
lean_dec_ref(v_____do__lift_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_t_3010_){
_start:
{
lean_object* v_toApplicative_3011_; lean_object* v_toBind_3012_; lean_object* v_getInfoState_3013_; lean_object* v_modifyInfoState_3014_; lean_object* v___f_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; 
v_toApplicative_3011_ = lean_ctor_get(v_inst_3008_, 0);
lean_inc_ref(v_toApplicative_3011_);
v_toBind_3012_ = lean_ctor_get(v_inst_3008_, 1);
lean_inc(v_toBind_3012_);
lean_dec_ref(v_inst_3008_);
v_getInfoState_3013_ = lean_ctor_get(v_inst_3009_, 0);
lean_inc(v_getInfoState_3013_);
v_modifyInfoState_3014_ = lean_ctor_get(v_inst_3009_, 1);
lean_inc(v_modifyInfoState_3014_);
lean_dec_ref(v_inst_3009_);
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3015_, 0, v_t_3010_);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3016_, 0, v_toApplicative_3011_);
lean_closure_set(v___f_3016_, 1, v_modifyInfoState_3014_);
lean_closure_set(v___f_3016_, 2, v___f_3015_);
v___x_3017_ = lean_apply_4(v_toBind_3012_, lean_box(0), lean_box(0), v_getInfoState_3013_, v___f_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_t_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3019_, v_inst_3020_, v_t_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_3023_, lean_object* v_t_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_____do__lift_3027_){
_start:
{
uint8_t v_enabled_3028_; 
v_enabled_3028_ = lean_ctor_get_uint8(v_____do__lift_3027_, sizeof(void*)*3);
if (v_enabled_3028_ == 0)
{
lean_object* v_toPure_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec_ref(v_inst_3026_);
lean_dec_ref(v_inst_3025_);
lean_dec_ref(v_t_3024_);
v_toPure_3029_ = lean_ctor_get(v_toApplicative_3023_, 1);
lean_inc(v_toPure_3029_);
lean_dec_ref(v_toApplicative_3023_);
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_apply_2(v_toPure_3029_, lean_box(0), v___x_3030_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref(v_toApplicative_3023_);
v___x_3032_ = lean_unsigned_to_nat(32u);
v___x_3033_ = lean_mk_empty_array_with_capacity(v___x_3032_);
lean_dec_ref(v___x_3033_);
v___x_3034_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3035_, 0, v_t_3024_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3025_, v_inst_3026_, v___x_3035_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_3037_, lean_object* v_t_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_____do__lift_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_3037_, v_t_3038_, v_inst_3039_, v_inst_3040_, v_____do__lift_3041_);
lean_dec_ref(v_____do__lift_3041_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_t_3045_){
_start:
{
lean_object* v_toApplicative_3046_; lean_object* v_toBind_3047_; lean_object* v_getInfoState_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; 
v_toApplicative_3046_ = lean_ctor_get(v_inst_3043_, 0);
lean_inc_ref(v_toApplicative_3046_);
v_toBind_3047_ = lean_ctor_get(v_inst_3043_, 1);
lean_inc(v_toBind_3047_);
v_getInfoState_3048_ = lean_ctor_get(v_inst_3044_, 0);
lean_inc(v_getInfoState_3048_);
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3049_, 0, v_toApplicative_3046_);
lean_closure_set(v___f_3049_, 1, v_t_3045_);
lean_closure_set(v___f_3049_, 2, v_inst_3043_);
lean_closure_set(v___f_3049_, 3, v_inst_3044_);
v___x_3050_ = lean_apply_4(v_toBind_3047_, lean_box(0), lean_box(0), v_getInfoState_3048_, v___f_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_t_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3052_, v_inst_3053_, v_t_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_info_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_info_3058_);
v___x_3060_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3056_, v_inst_3057_, v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_info_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3062_, v_inst_3063_, v_info_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3066_, lean_object* v_expectedType_x3f_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_____do__lift_3070_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_stx_3066_);
v___x_3073_ = l_Lean_LocalContext_empty;
v___x_3074_ = 0;
v___x_3075_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3075_, 0, v___x_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
lean_ctor_set(v___x_3075_, 2, v_expectedType_x3f_3067_);
lean_ctor_set(v___x_3075_, 3, v_____do__lift_3070_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*4, v___x_3074_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*4 + 1, v___x_3074_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
v___x_3077_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3068_, v_inst_3069_, v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v_stx_3082_, lean_object* v_n_3083_, lean_object* v_expectedType_x3f_3084_){
_start:
{
lean_object* v_toBind_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_toBind_3085_ = lean_ctor_get(v_inst_3078_, 1);
lean_inc(v_toBind_3085_);
lean_inc_ref(v_inst_3078_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3086_, 0, v_stx_3082_);
lean_closure_set(v___f_3086_, 1, v_expectedType_x3f_3084_);
lean_closure_set(v___f_3086_, 2, v_inst_3078_);
lean_closure_set(v___f_3086_, 3, v_inst_3079_);
v___x_3087_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3078_, v_inst_3080_, v_inst_3081_, v_n_3083_);
v___x_3088_ = lean_apply_4(v_toBind_3085_, lean_box(0), lean_box(0), v___x_3087_, v___f_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_stx_3094_, lean_object* v_n_3095_, lean_object* v_expectedType_x3f_3096_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3090_, v_inst_3091_, v_inst_3092_, v_inst_3093_, v_stx_3094_, v_n_3095_, v_expectedType_x3f_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v_infoState_3102_; uint8_t v_enabled_3103_; 
v___x_3101_ = lean_st_ref_get(v___y_3099_);
v_infoState_3102_ = lean_ctor_get(v___x_3101_, 7);
lean_inc_ref(v_infoState_3102_);
lean_dec(v___x_3101_);
v_enabled_3103_ = lean_ctor_get_uint8(v_infoState_3102_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3102_);
if (v_enabled_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec_ref(v_t_3098_);
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v_infoState_3107_; lean_object* v_env_3108_; lean_object* v_nextMacroScope_3109_; lean_object* v_ngen_3110_; lean_object* v_auxDeclNGen_3111_; lean_object* v_traceState_3112_; lean_object* v_cache_3113_; lean_object* v_messages_3114_; lean_object* v_snapshotTasks_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3137_; 
v___x_3106_ = lean_st_ref_take(v___y_3099_);
v_infoState_3107_ = lean_ctor_get(v___x_3106_, 7);
v_env_3108_ = lean_ctor_get(v___x_3106_, 0);
v_nextMacroScope_3109_ = lean_ctor_get(v___x_3106_, 1);
v_ngen_3110_ = lean_ctor_get(v___x_3106_, 2);
v_auxDeclNGen_3111_ = lean_ctor_get(v___x_3106_, 3);
v_traceState_3112_ = lean_ctor_get(v___x_3106_, 4);
v_cache_3113_ = lean_ctor_get(v___x_3106_, 5);
v_messages_3114_ = lean_ctor_get(v___x_3106_, 6);
v_snapshotTasks_3115_ = lean_ctor_get(v___x_3106_, 8);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3117_ = v___x_3106_;
v_isShared_3118_ = v_isSharedCheck_3137_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snapshotTasks_3115_);
lean_inc(v_infoState_3107_);
lean_inc(v_messages_3114_);
lean_inc(v_cache_3113_);
lean_inc(v_traceState_3112_);
lean_inc(v_auxDeclNGen_3111_);
lean_inc(v_ngen_3110_);
lean_inc(v_nextMacroScope_3109_);
lean_inc(v_env_3108_);
lean_dec(v___x_3106_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3137_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
uint8_t v_enabled_3119_; lean_object* v_assignment_3120_; lean_object* v_lazyAssignment_3121_; lean_object* v_trees_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3136_; 
v_enabled_3119_ = lean_ctor_get_uint8(v_infoState_3107_, sizeof(void*)*3);
v_assignment_3120_ = lean_ctor_get(v_infoState_3107_, 0);
v_lazyAssignment_3121_ = lean_ctor_get(v_infoState_3107_, 1);
v_trees_3122_ = lean_ctor_get(v_infoState_3107_, 2);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_infoState_3107_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3124_ = v_infoState_3107_;
v_isShared_3125_ = v_isSharedCheck_3136_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_trees_3122_);
lean_inc(v_lazyAssignment_3121_);
lean_inc(v_assignment_3120_);
lean_dec(v_infoState_3107_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3136_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = l_Lean_PersistentArray_push___redArg(v_trees_3122_, v_t_3098_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 2, v___x_3126_);
v___x_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_assignment_3120_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_lazyAssignment_3121_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v___x_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3135_, sizeof(void*)*3, v_enabled_3119_);
v___x_3128_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 7, v___x_3128_);
v___x_3130_ = v___x_3117_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_env_3108_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_nextMacroScope_3109_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_ngen_3110_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_auxDeclNGen_3111_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_traceState_3112_);
lean_ctor_set(v_reuseFailAlloc_3134_, 5, v_cache_3113_);
lean_ctor_set(v_reuseFailAlloc_3134_, 6, v_messages_3114_);
lean_ctor_set(v_reuseFailAlloc_3134_, 7, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3134_, 8, v_snapshotTasks_3115_);
v___x_3130_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_st_ref_set(v___y_3099_, v___x_3130_);
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3138_, v___y_3139_);
lean_dec(v___y_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v_infoState_3147_; uint8_t v_enabled_3148_; 
v___x_3146_ = lean_st_ref_get(v___y_3144_);
v_infoState_3147_ = lean_ctor_get(v___x_3146_, 7);
lean_inc_ref(v_infoState_3147_);
lean_dec(v___x_3146_);
v_enabled_3148_ = lean_ctor_get_uint8(v_infoState_3147_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3147_);
if (v_enabled_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v_t_3142_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3151_ = lean_unsigned_to_nat(32u);
v___x_3152_ = lean_mk_empty_array_with_capacity(v___x_3151_);
lean_dec_ref(v___x_3152_);
v___x_3153_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_t_3142_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3154_, v___y_3144_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
return v_res_3160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
lean_ctor_set(v___x_3166_, 3, v___x_3165_);
lean_ctor_set(v___x_3166_, 4, v___x_3164_);
lean_ctor_set(v___x_3166_, 5, v___x_3164_);
lean_ctor_set(v___x_3166_, 6, v___x_3164_);
lean_ctor_set(v___x_3166_, 7, v___x_3164_);
lean_ctor_set(v___x_3166_, 8, v___x_3164_);
lean_ctor_set(v___x_3166_, 9, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_box(1);
v___x_3168_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3169_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3167_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3173_ = l_Lean_stringToMessageData(v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3179_ = l_Lean_stringToMessageData(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3192_, lean_object* v_declHint_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v_env_3197_; uint8_t v___x_3198_; 
v___x_3196_ = lean_st_ref_get(v___y_3194_);
v_env_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc_ref(v_env_3197_);
lean_dec(v___x_3196_);
v___x_3198_ = l_Lean_Name_isAnonymous(v_declHint_3193_);
if (v___x_3198_ == 0)
{
uint8_t v_isExporting_3199_; 
v_isExporting_3199_ = lean_ctor_get_uint8(v_env_3197_, sizeof(void*)*8);
if (v_isExporting_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec_ref(v_env_3197_);
lean_dec(v_declHint_3193_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_msg_3192_);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; uint8_t v___x_3202_; 
lean_inc_ref(v_env_3197_);
v___x_3201_ = l_Lean_Environment_setExporting(v_env_3197_, v___x_3198_);
lean_inc(v_declHint_3193_);
lean_inc_ref(v___x_3201_);
v___x_3202_ = l_Lean_Environment_contains(v___x_3201_, v_declHint_3193_, v_isExporting_3199_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_env_3197_);
lean_dec(v_declHint_3193_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_msg_3192_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_c_3209_; lean_object* v___x_3210_; 
v___x_3204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3206_ = l_Lean_Options_empty;
v___x_3207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3201_);
lean_ctor_set(v___x_3207_, 1, v___x_3204_);
lean_ctor_set(v___x_3207_, 2, v___x_3205_);
lean_ctor_set(v___x_3207_, 3, v___x_3206_);
lean_inc(v_declHint_3193_);
v___x_3208_ = l_Lean_MessageData_ofConstName(v_declHint_3193_, v___x_3198_);
v_c_3209_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3209_, 0, v___x_3207_);
lean_ctor_set(v_c_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3197_, v_declHint_3193_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec_ref(v_env_3197_);
lean_dec(v_declHint_3193_);
v___x_3211_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v_c_3209_);
v___x_3213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = l_Lean_MessageData_note(v___x_3214_);
v___x_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_msg_3192_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
else
{
lean_object* v_val_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3253_; 
v_val_3218_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3220_ = v___x_3210_;
v_isShared_3221_ = v_isSharedCheck_3253_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_val_3218_);
lean_dec(v___x_3210_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3253_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_mod_3225_; uint8_t v___x_3226_; 
v___x_3222_ = lean_box(0);
v___x_3223_ = l_Lean_Environment_header(v_env_3197_);
lean_dec_ref(v_env_3197_);
v___x_3224_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3223_);
v_mod_3225_ = lean_array_get(v___x_3222_, v___x_3224_, v_val_3218_);
lean_dec(v_val_3218_);
lean_dec_ref(v___x_3224_);
v___x_3226_ = l_Lean_isPrivateName(v_declHint_3193_);
lean_dec(v_declHint_3193_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v_c_3209_);
v___x_3229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_MessageData_ofName(v_mod_3225_);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = l_Lean_MessageData_note(v___x_3234_);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v_msg_3192_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3236_);
v___x_3238_ = v___x_3220_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v_c_3209_);
v___x_3242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_MessageData_ofName(v_mod_3225_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_MessageData_note(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_msg_3192_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3249_);
v___x_3251_ = v___x_3220_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3254_; 
lean_dec_ref(v_env_3197_);
lean_dec(v_declHint_3193_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_msg_3192_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3255_, lean_object* v_declHint_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3255_, v_declHint_3256_, v___y_3257_);
lean_dec(v___y_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3260_, lean_object* v_declHint_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3275_; 
v___x_3265_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3260_, v_declHint_3261_, v___y_3263_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3270_ = l_Lean_unknownIdentifierMessageTag;
v___x_3271_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v_a_3266_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3271_);
v___x_3273_ = v___x_3268_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3276_, lean_object* v_declHint_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3276_, v_declHint_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; lean_object* v_env_3287_; lean_object* v_options_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3286_ = lean_st_ref_get(v___y_3284_);
v_env_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc_ref(v_env_3287_);
lean_dec(v___x_3286_);
v_options_3288_ = lean_ctor_get(v___y_3283_, 2);
v___x_3289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3290_ = lean_unsigned_to_nat(32u);
v___x_3291_ = lean_mk_empty_array_with_capacity(v___x_3290_);
lean_dec_ref(v___x_3291_);
v___x_3292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3288_);
v___x_3293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3293_, 0, v_env_3287_);
lean_ctor_set(v___x_3293_, 1, v___x_3289_);
lean_ctor_set(v___x_3293_, 2, v___x_3292_);
lean_ctor_set(v___x_3293_, 3, v_options_3288_);
v___x_3294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_msgData_3282_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_ref_3305_; lean_object* v___x_3306_; lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_ref_3305_ = lean_ctor_get(v___y_3302_, 5);
v___x_3306_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3301_, v___y_3302_, v___y_3303_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_inc(v_ref_3305_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_ref_3305_);
lean_ctor_set(v___x_3311_, 1, v_a_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 1);
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3321_, lean_object* v_msg_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_fileName_3326_; lean_object* v_fileMap_3327_; lean_object* v_options_3328_; lean_object* v_currRecDepth_3329_; lean_object* v_maxRecDepth_3330_; lean_object* v_ref_3331_; lean_object* v_currNamespace_3332_; lean_object* v_openDecls_3333_; lean_object* v_initHeartbeats_3334_; lean_object* v_maxHeartbeats_3335_; lean_object* v_quotContext_3336_; lean_object* v_currMacroScope_3337_; uint8_t v_diag_3338_; lean_object* v_cancelTk_x3f_3339_; uint8_t v_suppressElabErrors_3340_; lean_object* v_inheritedTraceOptions_3341_; lean_object* v_ref_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_fileName_3326_ = lean_ctor_get(v___y_3323_, 0);
v_fileMap_3327_ = lean_ctor_get(v___y_3323_, 1);
v_options_3328_ = lean_ctor_get(v___y_3323_, 2);
v_currRecDepth_3329_ = lean_ctor_get(v___y_3323_, 3);
v_maxRecDepth_3330_ = lean_ctor_get(v___y_3323_, 4);
v_ref_3331_ = lean_ctor_get(v___y_3323_, 5);
v_currNamespace_3332_ = lean_ctor_get(v___y_3323_, 6);
v_openDecls_3333_ = lean_ctor_get(v___y_3323_, 7);
v_initHeartbeats_3334_ = lean_ctor_get(v___y_3323_, 8);
v_maxHeartbeats_3335_ = lean_ctor_get(v___y_3323_, 9);
v_quotContext_3336_ = lean_ctor_get(v___y_3323_, 10);
v_currMacroScope_3337_ = lean_ctor_get(v___y_3323_, 11);
v_diag_3338_ = lean_ctor_get_uint8(v___y_3323_, sizeof(void*)*14);
v_cancelTk_x3f_3339_ = lean_ctor_get(v___y_3323_, 12);
v_suppressElabErrors_3340_ = lean_ctor_get_uint8(v___y_3323_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3341_ = lean_ctor_get(v___y_3323_, 13);
v_ref_3342_ = l_Lean_replaceRef(v_ref_3321_, v_ref_3331_);
lean_inc_ref(v_inheritedTraceOptions_3341_);
lean_inc(v_cancelTk_x3f_3339_);
lean_inc(v_currMacroScope_3337_);
lean_inc(v_quotContext_3336_);
lean_inc(v_maxHeartbeats_3335_);
lean_inc(v_initHeartbeats_3334_);
lean_inc(v_openDecls_3333_);
lean_inc(v_currNamespace_3332_);
lean_inc(v_maxRecDepth_3330_);
lean_inc(v_currRecDepth_3329_);
lean_inc_ref(v_options_3328_);
lean_inc_ref(v_fileMap_3327_);
lean_inc_ref(v_fileName_3326_);
v___x_3343_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3343_, 0, v_fileName_3326_);
lean_ctor_set(v___x_3343_, 1, v_fileMap_3327_);
lean_ctor_set(v___x_3343_, 2, v_options_3328_);
lean_ctor_set(v___x_3343_, 3, v_currRecDepth_3329_);
lean_ctor_set(v___x_3343_, 4, v_maxRecDepth_3330_);
lean_ctor_set(v___x_3343_, 5, v_ref_3342_);
lean_ctor_set(v___x_3343_, 6, v_currNamespace_3332_);
lean_ctor_set(v___x_3343_, 7, v_openDecls_3333_);
lean_ctor_set(v___x_3343_, 8, v_initHeartbeats_3334_);
lean_ctor_set(v___x_3343_, 9, v_maxHeartbeats_3335_);
lean_ctor_set(v___x_3343_, 10, v_quotContext_3336_);
lean_ctor_set(v___x_3343_, 11, v_currMacroScope_3337_);
lean_ctor_set(v___x_3343_, 12, v_cancelTk_x3f_3339_);
lean_ctor_set(v___x_3343_, 13, v_inheritedTraceOptions_3341_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*14, v_diag_3338_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*14 + 1, v_suppressElabErrors_3340_);
v___x_3344_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3322_, v___x_3343_, v___y_3324_);
lean_dec_ref(v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3345_, lean_object* v_msg_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3345_, v_msg_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v_ref_3345_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3351_, lean_object* v_msg_3352_, lean_object* v_declHint_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v___x_3359_; 
v___x_3357_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3352_, v_declHint_3353_, v___y_3354_, v___y_3355_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3351_, v_a_3358_, v___y_3354_, v___y_3355_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3360_, lean_object* v_msg_3361_, lean_object* v_declHint_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3360_, v_msg_3361_, v_declHint_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v_ref_3360_);
return v_res_3366_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3369_ = l_Lean_stringToMessageData(v___x_3368_);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3373_, lean_object* v_constName_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3378_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3379_ = 0;
lean_inc(v_constName_3374_);
v___x_3380_ = l_Lean_MessageData_ofConstName(v_constName_3374_, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3378_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3373_, v___x_3383_, v_constName_3374_, v___y_3375_, v___y_3376_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3385_, lean_object* v_constName_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3385_, v_constName_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v_ref_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_ref_3395_; lean_object* v___x_3396_; 
v_ref_3395_ = lean_ctor_get(v___y_3392_, 5);
v___x_3396_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3395_, v_constName_3391_, v___y_3392_, v___y_3393_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v_env_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; 
v___x_3406_ = lean_st_ref_get(v___y_3404_);
v_env_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc_ref(v_env_3407_);
lean_dec(v___x_3406_);
v___x_3408_ = 0;
lean_inc(v_constName_3402_);
v___x_3409_ = l_Lean_Environment_findConstVal_x3f(v_env_3407_, v_constName_3402_, v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3402_, v___y_3403_, v___y_3404_);
return v___x_3410_;
}
else
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_constName_3402_);
v_val_3411_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3409_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v___x_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_val_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
if (lean_obj_tag(v_a_3424_) == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = l_List_reverse___redArg(v_a_3425_);
return v___x_3426_;
}
else
{
lean_object* v_head_3427_; lean_object* v_tail_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3437_; 
v_head_3427_ = lean_ctor_get(v_a_3424_, 0);
v_tail_3428_ = lean_ctor_get(v_a_3424_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_a_3424_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3430_ = v_a_3424_;
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_tail_3428_);
lean_inc(v_head_3427_);
lean_dec(v_a_3424_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = l_Lean_mkLevelParam(v_head_3427_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_a_3425_);
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_a_3425_);
v___x_3434_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
v_a_3424_ = v_tail_3428_;
v_a_3425_ = v___x_3434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
lean_inc(v_constName_3438_);
v___x_3442_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3454_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_levelParams_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v_levelParams_3447_ = lean_ctor_get(v_a_3443_, 1);
lean_inc(v_levelParams_3447_);
lean_dec(v_a_3443_);
v___x_3448_ = lean_box(0);
v___x_3449_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3447_, v___x_3448_);
v___x_3450_ = l_Lean_mkConst(v_constName_3438_, v___x_3449_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3450_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v_constName_3438_);
v_a_3455_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3442_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3442_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3468_, lean_object* v_n_3469_, lean_object* v_expectedType_x3f_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3469_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v_stx_3468_);
v___x_3478_ = l_Lean_LocalContext_empty;
v___x_3479_ = 0;
v___x_3480_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3480_, 0, v___x_3477_);
lean_ctor_set(v___x_3480_, 1, v___x_3478_);
lean_ctor_set(v___x_3480_, 2, v_expectedType_x3f_3470_);
lean_ctor_set(v___x_3480_, 3, v_a_3475_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*4, v___x_3479_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*4 + 1, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3481_, v___y_3471_, v___y_3472_);
return v___x_3482_;
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v_expectedType_x3f_3470_);
lean_dec(v_stx_3468_);
v_a_3483_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3474_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3474_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3491_, lean_object* v_n_3492_, lean_object* v_expectedType_x3f_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3491_, v_n_3492_, v_expectedType_x3f_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3498_, lean_object* v_expectedType_x3f_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v___x_3503_; 
lean_inc(v_id_3498_);
v___x_3503_ = l_Lean_realizeGlobalConstNoOverload(v_id_3498_, v_a_3500_, v_a_3501_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3531_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3531_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3531_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v_infoState_3509_; uint8_t v_enabled_3510_; 
v___x_3508_ = lean_st_ref_get(v_a_3501_);
v_infoState_3509_ = lean_ctor_get(v___x_3508_, 7);
lean_inc_ref(v_infoState_3509_);
lean_dec(v___x_3508_);
v_enabled_3510_ = lean_ctor_get_uint8(v_infoState_3509_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3509_);
if (v_enabled_3510_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v_expectedType_x3f_3499_);
lean_dec(v_id_3498_);
if (v_isShared_3507_ == 0)
{
v___x_3512_ = v___x_3506_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3504_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
else
{
lean_object* v___x_3514_; 
lean_del_object(v___x_3506_);
lean_inc(v_a_3504_);
v___x_3514_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3498_, v_a_3504_, v_expectedType_x3f_3499_, v_a_3500_, v_a_3501_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v___x_3514_, 0);
lean_dec(v_unused_3522_);
v___x_3516_ = v___x_3514_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_dec(v___x_3514_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v_a_3504_);
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3504_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_a_3504_);
v_a_3523_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3514_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3514_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3499_);
lean_dec(v_id_3498_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3532_, lean_object* v_expectedType_x3f_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3532_, v_expectedType_x3f_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3538_, v___y_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3548_, lean_object* v_constName_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3549_, v___y_3550_, v___y_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3554_, lean_object* v_constName_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3554_, v_constName_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3560_, lean_object* v_ref_3561_, lean_object* v_constName_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3561_, v_constName_3562_, v___y_3563_, v___y_3564_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3567_, lean_object* v_ref_3568_, lean_object* v_constName_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3567_, v_ref_3568_, v_constName_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v_ref_3568_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3574_, lean_object* v_ref_3575_, lean_object* v_msg_3576_, lean_object* v_declHint_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3575_, v_msg_3576_, v_declHint_3577_, v___y_3578_, v___y_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_ref_3583_, lean_object* v_msg_3584_, lean_object* v_declHint_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3582_, v_ref_3583_, v_msg_3584_, v_declHint_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v_ref_3583_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3590_, lean_object* v_declHint_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3590_, v_declHint_3591_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3596_, lean_object* v_declHint_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3596_, v_declHint_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3602_, lean_object* v_ref_3603_, lean_object* v_msg_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3603_, v_msg_3604_, v___y_3605_, v___y_3606_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3609_, lean_object* v_ref_3610_, lean_object* v_msg_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3609_, v_ref_3610_, v_msg_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v_ref_3610_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3616_, lean_object* v_msg_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3617_, v___y_3618_, v___y_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3622_, lean_object* v_msg_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3622_, v_msg_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3628_, lean_object* v_expectedType_x3f_3629_, lean_object* v_as_x27_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
if (lean_obj_tag(v_as_x27_3630_) == 0)
{
lean_object* v___x_3635_; 
lean_dec(v_expectedType_x3f_3629_);
lean_dec(v_id_3628_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_b_3631_);
return v___x_3635_;
}
else
{
lean_object* v_head_3636_; lean_object* v_tail_3637_; lean_object* v___x_3638_; 
v_head_3636_ = lean_ctor_get(v_as_x27_3630_, 0);
v_tail_3637_ = lean_ctor_get(v_as_x27_3630_, 1);
lean_inc(v_expectedType_x3f_3629_);
lean_inc(v_head_3636_);
lean_inc(v_id_3628_);
v___x_3638_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3628_, v_head_3636_, v_expectedType_x3f_3629_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v___x_3639_; 
lean_dec_ref(v___x_3638_);
v___x_3639_ = lean_box(0);
v_as_x27_3630_ = v_tail_3637_;
v_b_3631_ = v___x_3639_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_3629_);
lean_dec(v_id_3628_);
return v___x_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3641_, lean_object* v_expectedType_x3f_3642_, lean_object* v_as_x27_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3641_, v_expectedType_x3f_3642_, v_as_x27_3643_, v_b_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v_as_x27_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3649_, lean_object* v_expectedType_x3f_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3654_; 
lean_inc(v_id_3649_);
v___x_3654_ = l_Lean_realizeGlobalConst(v_id_3649_, v_a_3651_, v_a_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3683_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3683_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3683_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v_infoState_3660_; uint8_t v_enabled_3661_; 
v___x_3659_ = lean_st_ref_get(v_a_3652_);
v_infoState_3660_ = lean_ctor_get(v___x_3659_, 7);
lean_inc_ref(v_infoState_3660_);
lean_dec(v___x_3659_);
v_enabled_3661_ = lean_ctor_get_uint8(v_infoState_3660_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3660_);
if (v_enabled_3661_ == 0)
{
lean_object* v___x_3663_; 
lean_dec(v_expectedType_x3f_3650_);
lean_dec(v_id_3649_);
if (v_isShared_3658_ == 0)
{
v___x_3663_ = v___x_3657_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3655_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
lean_del_object(v___x_3657_);
v___x_3665_ = lean_box(0);
v___x_3666_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3649_, v_expectedType_x3f_3650_, v_a_3655_, v___x_3665_, v_a_3651_, v_a_3652_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___x_3666_, 0);
lean_dec(v_unused_3674_);
v___x_3668_ = v___x_3666_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v___x_3666_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v_a_3655_);
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3655_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_a_3655_);
v_a_3675_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3666_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3666_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3650_);
lean_dec(v_id_3649_);
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3684_, lean_object* v_expectedType_x3f_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3684_, v_expectedType_x3f_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3690_, lean_object* v_expectedType_x3f_3691_, lean_object* v_as_3692_, lean_object* v_as_x27_3693_, lean_object* v_b_3694_, lean_object* v_a_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3690_, v_expectedType_x3f_3691_, v_as_x27_3693_, v_b_3694_, v___y_3696_, v___y_3697_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3700_, lean_object* v_expectedType_x3f_3701_, lean_object* v_as_3702_, lean_object* v_as_x27_3703_, lean_object* v_b_3704_, lean_object* v_a_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3700_, v_expectedType_x3f_3701_, v_as_3702_, v_as_x27_3703_, v_b_3704_, v_a_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v_as_x27_3703_);
lean_dec(v_as_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3710_, lean_object* v_as_x27_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
if (lean_obj_tag(v_as_x27_3711_) == 0)
{
lean_object* v___x_3716_; 
lean_dec(v_ref_3710_);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_b_3712_);
return v___x_3716_;
}
else
{
lean_object* v_head_3717_; lean_object* v_tail_3718_; lean_object* v_fst_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_head_3717_ = lean_ctor_get(v_as_x27_3711_, 0);
v_tail_3718_ = lean_ctor_get(v_as_x27_3711_, 1);
v_fst_3719_ = lean_ctor_get(v_head_3717_, 0);
v___x_3720_ = lean_box(0);
lean_inc(v_fst_3719_);
lean_inc(v_ref_3710_);
v___x_3721_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3710_, v_fst_3719_, v___x_3720_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; 
lean_dec_ref(v___x_3721_);
v___x_3722_ = lean_box(0);
v_as_x27_3711_ = v_tail_3718_;
v_b_3712_ = v___x_3722_;
goto _start;
}
else
{
lean_dec(v_ref_3710_);
return v___x_3721_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3724_, lean_object* v_as_x27_3725_, lean_object* v_b_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3724_, v_as_x27_3725_, v_b_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v_as_x27_3725_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3731_, lean_object* v_id_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_realizeGlobalName(v_id_3732_, v_a_3733_, v_a_3734_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3765_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3765_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3765_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v_infoState_3742_; uint8_t v_enabled_3743_; 
v___x_3741_ = lean_st_ref_get(v_a_3734_);
v_infoState_3742_ = lean_ctor_get(v___x_3741_, 7);
lean_inc_ref(v_infoState_3742_);
lean_dec(v___x_3741_);
v_enabled_3743_ = lean_ctor_get_uint8(v_infoState_3742_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3742_);
if (v_enabled_3743_ == 0)
{
lean_object* v___x_3745_; 
lean_dec(v_ref_3731_);
if (v_isShared_3740_ == 0)
{
v___x_3745_ = v___x_3739_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3737_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_del_object(v___x_3739_);
v___x_3747_ = lean_box(0);
v___x_3748_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3731_, v_a_3737_, v___x_3747_, v_a_3733_, v_a_3734_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3756_);
v___x_3750_ = v___x_3748_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v___x_3748_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_a_3737_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3737_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3737_);
v_a_3757_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3748_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3748_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_3731_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3766_, lean_object* v_id_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3766_, v_id_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3772_, lean_object* v_as_3773_, lean_object* v_as_x27_3774_, lean_object* v_b_3775_, lean_object* v_a_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3772_, v_as_x27_3774_, v_b_3775_, v___y_3777_, v___y_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3781_, lean_object* v_as_3782_, lean_object* v_as_x27_3783_, lean_object* v_b_3784_, lean_object* v_a_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3781_, v_as_3782_, v_as_x27_3783_, v_b_3784_, v_a_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v_as_x27_3783_);
lean_dec(v_as_3782_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3790_){
_start:
{
lean_object* v_fst_3791_; 
v_fst_3791_ = lean_ctor_get(v_self_3790_, 0);
lean_inc(v_fst_3791_);
return v_fst_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3792_);
lean_dec_ref(v_self_3792_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3794_, lean_object* v_treesSaved_3795_, lean_object* v_s_3796_){
_start:
{
if (lean_obj_tag(v_info_3794_) == 0)
{
uint8_t v_enabled_3797_; lean_object* v_assignment_3798_; lean_object* v_lazyAssignment_3799_; lean_object* v_trees_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3810_; 
v_enabled_3797_ = lean_ctor_get_uint8(v_s_3796_, sizeof(void*)*3);
v_assignment_3798_ = lean_ctor_get(v_s_3796_, 0);
v_lazyAssignment_3799_ = lean_ctor_get(v_s_3796_, 1);
v_trees_3800_ = lean_ctor_get(v_s_3796_, 2);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_s_3796_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3802_ = v_s_3796_;
v_isShared_3803_ = v_isSharedCheck_3810_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_trees_3800_);
lean_inc(v_lazyAssignment_3799_);
lean_inc(v_assignment_3798_);
lean_dec(v_s_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3810_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_val_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v_val_3804_ = lean_ctor_get(v_info_3794_, 0);
lean_inc(v_val_3804_);
lean_dec_ref(v_info_3794_);
v___x_3805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3805_, 0, v_val_3804_);
lean_ctor_set(v___x_3805_, 1, v_trees_3800_);
v___x_3806_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3795_, v___x_3805_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 2, v___x_3806_);
v___x_3808_ = v___x_3802_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_assignment_3798_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_lazyAssignment_3799_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v___x_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, sizeof(void*)*3, v_enabled_3797_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
else
{
uint8_t v_enabled_3811_; lean_object* v_assignment_3812_; lean_object* v_lazyAssignment_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3829_; 
v_enabled_3811_ = lean_ctor_get_uint8(v_s_3796_, sizeof(void*)*3);
v_assignment_3812_ = lean_ctor_get(v_s_3796_, 0);
v_lazyAssignment_3813_ = lean_ctor_get(v_s_3796_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_s_3796_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; 
v_unused_3830_ = lean_ctor_get(v_s_3796_, 2);
lean_dec(v_unused_3830_);
v___x_3815_ = v_s_3796_;
v_isShared_3816_ = v_isSharedCheck_3829_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_lazyAssignment_3813_);
lean_inc(v_assignment_3812_);
lean_dec(v_s_3796_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3829_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v_val_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3828_; 
v_val_3817_ = lean_ctor_get(v_info_3794_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_info_3794_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3819_ = v_info_3794_;
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_val_3817_);
lean_dec(v_info_3794_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 2);
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_val_3817_);
v___x_3822_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3795_, v___x_3822_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 2, v___x_3823_);
v___x_3825_ = v___x_3815_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_assignment_3812_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_lazyAssignment_3813_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v___x_3823_);
lean_ctor_set_uint8(v_reuseFailAlloc_3826_, sizeof(void*)*3, v_enabled_3811_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3831_, lean_object* v_modifyInfoState_3832_, lean_object* v_info_3833_){
_start:
{
lean_object* v___f_3834_; lean_object* v___x_3835_; 
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3834_, 0, v_info_3833_);
lean_closure_set(v___f_3834_, 1, v_treesSaved_3831_);
v___x_3835_ = lean_apply_1(v_modifyInfoState_3832_, v___f_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3836_, lean_object* v_info_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_apply_1(v___f_3836_, v_info_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3839_, lean_object* v_toBind_3840_, lean_object* v___f_3841_, lean_object* v_____do__lift_3842_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_____do__lift_3842_);
v___x_3844_ = lean_apply_2(v_toPure_3839_, lean_box(0), v___x_3843_);
v___x_3845_ = lean_apply_4(v_toBind_3840_, lean_box(0), lean_box(0), v___x_3844_, v___f_3841_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3846_, lean_object* v_mkInfoOnError_3847_, lean_object* v___f_3848_, lean_object* v_mkInfo_3849_, lean_object* v___f_3850_, lean_object* v_a_x3f_3851_){
_start:
{
if (lean_obj_tag(v_a_x3f_3851_) == 0)
{
lean_object* v___x_3852_; 
lean_dec(v___f_3850_);
lean_dec(v_mkInfo_3849_);
v___x_3852_ = lean_apply_4(v_toBind_3846_, lean_box(0), lean_box(0), v_mkInfoOnError_3847_, v___f_3848_);
return v___x_3852_;
}
else
{
lean_object* v_val_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v___f_3848_);
lean_dec(v_mkInfoOnError_3847_);
v_val_3853_ = lean_ctor_get(v_a_x3f_3851_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v_a_x3f_3851_);
v___x_3854_ = lean_apply_1(v_mkInfo_3849_, v_val_3853_);
v___x_3855_ = lean_apply_4(v_toBind_3846_, lean_box(0), lean_box(0), v___x_3854_, v___f_3850_);
return v___x_3855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3856_, lean_object* v_modifyInfoState_3857_, lean_object* v_toBind_3858_, lean_object* v_mkInfoOnError_3859_, lean_object* v_mkInfo_3860_, lean_object* v_inst_3861_, lean_object* v_x_3862_, lean_object* v___f_3863_, lean_object* v_treesSaved_3864_){
_start:
{
lean_object* v_toFunctor_3865_; lean_object* v_toPure_3866_; lean_object* v_map_3867_; lean_object* v___f_3868_; lean_object* v___f_3869_; lean_object* v___f_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_toFunctor_3865_ = lean_ctor_get(v_toApplicative_3856_, 0);
lean_inc_ref(v_toFunctor_3865_);
v_toPure_3866_ = lean_ctor_get(v_toApplicative_3856_, 1);
lean_inc(v_toPure_3866_);
lean_dec_ref(v_toApplicative_3856_);
v_map_3867_ = lean_ctor_get(v_toFunctor_3865_, 0);
lean_inc(v_map_3867_);
lean_dec_ref(v_toFunctor_3865_);
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3868_, 0, v_treesSaved_3864_);
lean_closure_set(v___f_3868_, 1, v_modifyInfoState_3857_);
v___f_3869_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3869_, 0, v___f_3868_);
lean_inc_ref(v___f_3869_);
lean_inc(v_toBind_3858_);
v___f_3870_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3870_, 0, v_toPure_3866_);
lean_closure_set(v___f_3870_, 1, v_toBind_3858_);
lean_closure_set(v___f_3870_, 2, v___f_3869_);
v___f_3871_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3871_, 0, v_toBind_3858_);
lean_closure_set(v___f_3871_, 1, v_mkInfoOnError_3859_);
lean_closure_set(v___f_3871_, 2, v___f_3870_);
lean_closure_set(v___f_3871_, 3, v_mkInfo_3860_);
lean_closure_set(v___f_3871_, 4, v___f_3869_);
v___x_3872_ = lean_apply_4(v_inst_3861_, lean_box(0), lean_box(0), v_x_3862_, v___f_3871_);
v___x_3873_ = lean_apply_4(v_map_3867_, lean_box(0), lean_box(0), v___f_3863_, v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3874_, lean_object* v_inst_3875_, lean_object* v_inst_3876_, lean_object* v_toBind_3877_, lean_object* v___f_3878_, lean_object* v_____do__lift_3879_){
_start:
{
uint8_t v_enabled_3880_; 
v_enabled_3880_ = lean_ctor_get_uint8(v_____do__lift_3879_, sizeof(void*)*3);
if (v_enabled_3880_ == 0)
{
lean_dec(v___f_3878_);
lean_dec(v_toBind_3877_);
lean_dec_ref(v_inst_3876_);
lean_dec_ref(v_inst_3875_);
lean_inc(v_x_3874_);
return v_x_3874_;
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3875_, v_inst_3876_);
v___x_3882_ = lean_apply_4(v_toBind_3877_, lean_box(0), lean_box(0), v___x_3881_, v___f_3878_);
return v___x_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3883_, lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_toBind_3886_, lean_object* v___f_3887_, lean_object* v_____do__lift_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3883_, v_inst_3884_, v_inst_3885_, v_toBind_3886_, v___f_3887_, v_____do__lift_3888_);
lean_dec_ref(v_____do__lift_3888_);
lean_dec(v_x_3883_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3891_, lean_object* v_inst_3892_, lean_object* v_inst_3893_, lean_object* v_x_3894_, lean_object* v_mkInfo_3895_, lean_object* v_mkInfoOnError_3896_){
_start:
{
lean_object* v_toApplicative_3897_; lean_object* v_toBind_3898_; lean_object* v_getInfoState_3899_; lean_object* v_modifyInfoState_3900_; lean_object* v___f_3901_; lean_object* v___f_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; 
v_toApplicative_3897_ = lean_ctor_get(v_inst_3891_, 0);
v_toBind_3898_ = lean_ctor_get(v_inst_3891_, 1);
lean_inc_n(v_toBind_3898_, 3);
v_getInfoState_3899_ = lean_ctor_get(v_inst_3892_, 0);
lean_inc(v_getInfoState_3899_);
v_modifyInfoState_3900_ = lean_ctor_get(v_inst_3892_, 1);
v___f_3901_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3894_);
lean_inc(v_modifyInfoState_3900_);
lean_inc_ref(v_toApplicative_3897_);
v___f_3902_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3902_, 0, v_toApplicative_3897_);
lean_closure_set(v___f_3902_, 1, v_modifyInfoState_3900_);
lean_closure_set(v___f_3902_, 2, v_toBind_3898_);
lean_closure_set(v___f_3902_, 3, v_mkInfoOnError_3896_);
lean_closure_set(v___f_3902_, 4, v_mkInfo_3895_);
lean_closure_set(v___f_3902_, 5, v_inst_3893_);
lean_closure_set(v___f_3902_, 6, v_x_3894_);
lean_closure_set(v___f_3902_, 7, v___f_3901_);
v___f_3903_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3903_, 0, v_x_3894_);
lean_closure_set(v___f_3903_, 1, v_inst_3891_);
lean_closure_set(v___f_3903_, 2, v_inst_3892_);
lean_closure_set(v___f_3903_, 3, v_toBind_3898_);
lean_closure_set(v___f_3903_, 4, v___f_3902_);
v___x_3904_ = lean_apply_4(v_toBind_3898_, lean_box(0), lean_box(0), v_getInfoState_3899_, v___f_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3905_, lean_object* v_inst_3906_, lean_object* v_inst_3907_, lean_object* v_00_u03b1_3908_, lean_object* v_inst_3909_, lean_object* v_x_3910_, lean_object* v_mkInfo_3911_, lean_object* v_mkInfoOnError_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3906_, v_inst_3907_, v_inst_3909_, v_x_3910_, v_mkInfo_3911_, v_mkInfoOnError_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3914_, lean_object* v_tree_3915_, lean_object* v_s_3916_){
_start:
{
uint8_t v_enabled_3917_; lean_object* v_assignment_3918_; lean_object* v_lazyAssignment_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3927_; 
v_enabled_3917_ = lean_ctor_get_uint8(v_s_3916_, sizeof(void*)*3);
v_assignment_3918_ = lean_ctor_get(v_s_3916_, 0);
v_lazyAssignment_3919_ = lean_ctor_get(v_s_3916_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_s_3916_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_s_3916_, 2);
lean_dec(v_unused_3928_);
v___x_3921_ = v_s_3916_;
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_lazyAssignment_3919_);
lean_inc(v_assignment_3918_);
lean_dec(v_s_3916_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3914_, v_tree_3915_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 2, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_assignment_3918_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_lazyAssignment_3919_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v___x_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, sizeof(void*)*3, v_enabled_3917_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3929_, lean_object* v_modifyInfoState_3930_, lean_object* v_tree_3931_){
_start:
{
lean_object* v___f_3932_; lean_object* v___x_3933_; 
v___f_3932_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3932_, 0, v_treesSaved_3929_);
lean_closure_set(v___f_3932_, 1, v_tree_3931_);
v___x_3933_ = lean_apply_1(v_modifyInfoState_3930_, v___f_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3934_, lean_object* v_toBind_3935_, lean_object* v___f_3936_, lean_object* v_st_3937_){
_start:
{
lean_object* v_trees_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_trees_3938_ = lean_ctor_get(v_st_3937_, 2);
lean_inc_ref(v_trees_3938_);
lean_dec_ref(v_st_3937_);
v___x_3939_ = lean_apply_1(v_mkInfoTree_3934_, v_trees_3938_);
v___x_3940_ = lean_apply_4(v_toBind_3935_, lean_box(0), lean_box(0), v___x_3939_, v___f_3936_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3941_, lean_object* v_getInfoState_3942_, lean_object* v___f_3943_, lean_object* v_x_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_apply_4(v_toBind_3941_, lean_box(0), lean_box(0), v_getInfoState_3942_, v___f_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3946_, lean_object* v_getInfoState_3947_, lean_object* v___f_3948_, lean_object* v_x_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3946_, v_getInfoState_3947_, v___f_3948_, v_x_3949_);
lean_dec(v_x_3949_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3951_, lean_object* v_modifyInfoState_3952_, lean_object* v_mkInfoTree_3953_, lean_object* v_toBind_3954_, lean_object* v_getInfoState_3955_, lean_object* v_inst_3956_, lean_object* v_x_3957_, lean_object* v___f_3958_, lean_object* v_treesSaved_3959_){
_start:
{
lean_object* v_toFunctor_3960_; lean_object* v_map_3961_; lean_object* v___f_3962_; lean_object* v___f_3963_; lean_object* v___f_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_toFunctor_3960_ = lean_ctor_get(v_toApplicative_3951_, 0);
lean_inc_ref(v_toFunctor_3960_);
lean_dec_ref(v_toApplicative_3951_);
v_map_3961_ = lean_ctor_get(v_toFunctor_3960_, 0);
lean_inc(v_map_3961_);
lean_dec_ref(v_toFunctor_3960_);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3962_, 0, v_treesSaved_3959_);
lean_closure_set(v___f_3962_, 1, v_modifyInfoState_3952_);
lean_inc(v_toBind_3954_);
v___f_3963_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3963_, 0, v_mkInfoTree_3953_);
lean_closure_set(v___f_3963_, 1, v_toBind_3954_);
lean_closure_set(v___f_3963_, 2, v___f_3962_);
v___f_3964_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3964_, 0, v_toBind_3954_);
lean_closure_set(v___f_3964_, 1, v_getInfoState_3955_);
lean_closure_set(v___f_3964_, 2, v___f_3963_);
v___x_3965_ = lean_apply_4(v_inst_3956_, lean_box(0), lean_box(0), v_x_3957_, v___f_3964_);
v___x_3966_ = lean_apply_4(v_map_3961_, lean_box(0), lean_box(0), v___f_3958_, v___x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3967_, lean_object* v_inst_3968_, lean_object* v_inst_3969_, lean_object* v_x_3970_, lean_object* v_mkInfoTree_3971_){
_start:
{
lean_object* v_toApplicative_3972_; lean_object* v_toBind_3973_; lean_object* v_getInfoState_3974_; lean_object* v_modifyInfoState_3975_; lean_object* v___f_3976_; lean_object* v___f_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; 
v_toApplicative_3972_ = lean_ctor_get(v_inst_3967_, 0);
v_toBind_3973_ = lean_ctor_get(v_inst_3967_, 1);
lean_inc_n(v_toBind_3973_, 3);
v_getInfoState_3974_ = lean_ctor_get(v_inst_3968_, 0);
lean_inc_n(v_getInfoState_3974_, 2);
v_modifyInfoState_3975_ = lean_ctor_get(v_inst_3968_, 1);
v___f_3976_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3970_);
lean_inc(v_modifyInfoState_3975_);
lean_inc_ref(v_toApplicative_3972_);
v___f_3977_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3977_, 0, v_toApplicative_3972_);
lean_closure_set(v___f_3977_, 1, v_modifyInfoState_3975_);
lean_closure_set(v___f_3977_, 2, v_mkInfoTree_3971_);
lean_closure_set(v___f_3977_, 3, v_toBind_3973_);
lean_closure_set(v___f_3977_, 4, v_getInfoState_3974_);
lean_closure_set(v___f_3977_, 5, v_inst_3969_);
lean_closure_set(v___f_3977_, 6, v_x_3970_);
lean_closure_set(v___f_3977_, 7, v___f_3976_);
v___f_3978_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3978_, 0, v_x_3970_);
lean_closure_set(v___f_3978_, 1, v_inst_3967_);
lean_closure_set(v___f_3978_, 2, v_inst_3968_);
lean_closure_set(v___f_3978_, 3, v_toBind_3973_);
lean_closure_set(v___f_3978_, 4, v___f_3977_);
v___x_3979_ = lean_apply_4(v_toBind_3973_, lean_box(0), lean_box(0), v_getInfoState_3974_, v___f_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3980_, lean_object* v_inst_3981_, lean_object* v_inst_3982_, lean_object* v_00_u03b1_3983_, lean_object* v_inst_3984_, lean_object* v_x_3985_, lean_object* v_mkInfoTree_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3981_, v_inst_3982_, v_inst_3984_, v_x_3985_, v_mkInfoTree_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3988_, lean_object* v_toPure_3989_, lean_object* v_____do__lift_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_____do__lift_3990_);
lean_ctor_set(v___x_3991_, 1, v_trees_3988_);
v___x_3992_ = lean_apply_2(v_toPure_3989_, lean_box(0), v___x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3993_, lean_object* v_toBind_3994_, lean_object* v_mkInfo_3995_, lean_object* v_trees_3996_){
_start:
{
lean_object* v___f_3997_; lean_object* v___x_3998_; 
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3997_, 0, v_trees_3996_);
lean_closure_set(v___f_3997_, 1, v_toPure_3993_);
v___x_3998_ = lean_apply_4(v_toBind_3994_, lean_box(0), lean_box(0), v_mkInfo_3995_, v___f_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3999_, lean_object* v_inst_4000_, lean_object* v_inst_4001_, lean_object* v_x_4002_, lean_object* v_mkInfo_4003_){
_start:
{
lean_object* v_toApplicative_4004_; lean_object* v_toBind_4005_; lean_object* v_toPure_4006_; lean_object* v___f_4007_; lean_object* v___x_4008_; 
v_toApplicative_4004_ = lean_ctor_get(v_inst_3999_, 0);
v_toBind_4005_ = lean_ctor_get(v_inst_3999_, 1);
v_toPure_4006_ = lean_ctor_get(v_toApplicative_4004_, 1);
lean_inc(v_toBind_4005_);
lean_inc(v_toPure_4006_);
v___f_4007_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4007_, 0, v_toPure_4006_);
lean_closure_set(v___f_4007_, 1, v_toBind_4005_);
lean_closure_set(v___f_4007_, 2, v_mkInfo_4003_);
v___x_4008_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3999_, v_inst_4000_, v_inst_4001_, v_x_4002_, v___f_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_4009_, lean_object* v_inst_4010_, lean_object* v_inst_4011_, lean_object* v_00_u03b1_4012_, lean_object* v_inst_4013_, lean_object* v_x_4014_, lean_object* v_mkInfo_4015_){
_start:
{
lean_object* v_toApplicative_4016_; lean_object* v_toBind_4017_; lean_object* v_toPure_4018_; lean_object* v___f_4019_; lean_object* v___x_4020_; 
v_toApplicative_4016_ = lean_ctor_get(v_inst_4010_, 0);
v_toBind_4017_ = lean_ctor_get(v_inst_4010_, 1);
v_toPure_4018_ = lean_ctor_get(v_toApplicative_4016_, 1);
lean_inc(v_toBind_4017_);
lean_inc(v_toPure_4018_);
v___f_4019_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4019_, 0, v_toPure_4018_);
lean_closure_set(v___f_4019_, 1, v_toBind_4017_);
lean_closure_set(v___f_4019_, 2, v_mkInfo_4015_);
v___x_4020_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4010_, v_inst_4011_, v_inst_4013_, v_x_4014_, v___f_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_4021_, lean_object* v_trees_4022_, lean_object* v_s_4023_){
_start:
{
uint8_t v_enabled_4024_; lean_object* v_assignment_4025_; lean_object* v_lazyAssignment_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4034_; 
v_enabled_4024_ = lean_ctor_get_uint8(v_s_4023_, sizeof(void*)*3);
v_assignment_4025_ = lean_ctor_get(v_s_4023_, 0);
v_lazyAssignment_4026_ = lean_ctor_get(v_s_4023_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_s_4023_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v_s_4023_, 2);
lean_dec(v_unused_4035_);
v___x_4028_ = v_s_4023_;
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_lazyAssignment_4026_);
lean_inc(v_assignment_4025_);
lean_dec(v_s_4023_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4030_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_4021_, v_trees_4022_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 2, v___x_4030_);
v___x_4032_ = v___x_4028_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_assignment_4025_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_lazyAssignment_4026_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v___x_4030_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, sizeof(void*)*3, v_enabled_4024_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_4036_, lean_object* v_trees_4037_, lean_object* v_s_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_4036_, v_trees_4037_, v_s_4038_);
lean_dec_ref(v_trees_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_4040_, lean_object* v_modifyInfoState_4041_, lean_object* v_trees_4042_){
_start:
{
lean_object* v___f_4043_; lean_object* v___x_4044_; 
v___f_4043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4043_, 0, v_treesSaved_4040_);
lean_closure_set(v___f_4043_, 1, v_trees_4042_);
v___x_4044_ = lean_apply_1(v_modifyInfoState_4041_, v___f_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_4045_, lean_object* v_tree_4046_, lean_object* v_____do__lift_4047_){
_start:
{
if (lean_obj_tag(v_____do__lift_4047_) == 0)
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_apply_2(v_toPure_4045_, lean_box(0), v_tree_4046_);
return v___x_4048_;
}
else
{
lean_object* v_val_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_val_4049_ = lean_ctor_get(v_____do__lift_4047_, 0);
lean_inc(v_val_4049_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v_val_4049_);
lean_ctor_set(v___x_4050_, 1, v_tree_4046_);
v___x_4051_ = lean_apply_2(v_toPure_4045_, lean_box(0), v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_4052_, lean_object* v_tree_4053_, lean_object* v_____do__lift_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_4052_, v_tree_4053_, v_____do__lift_4054_);
lean_dec(v_____do__lift_4054_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4056_, lean_object* v_toPure_4057_, lean_object* v_toBind_4058_, lean_object* v_ctx_x3f_4059_, lean_object* v_tree_4060_){
_start:
{
lean_object* v_tree_4061_; lean_object* v___f_4062_; lean_object* v___x_4063_; 
v_tree_4061_ = l_Lean_Elab_InfoTree_substitute(v_tree_4060_, v_assignment_4056_);
v___f_4062_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4062_, 0, v_toPure_4057_);
lean_closure_set(v___f_4062_, 1, v_tree_4061_);
v___x_4063_ = lean_apply_4(v_toBind_4058_, lean_box(0), lean_box(0), v_ctx_x3f_4059_, v___f_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_4064_, lean_object* v_toPure_4065_, lean_object* v_toBind_4066_, lean_object* v_ctx_x3f_4067_, lean_object* v_tree_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_4064_, v_toPure_4065_, v_toBind_4066_, v_ctx_x3f_4067_, v_tree_4068_);
lean_dec_ref(v_assignment_4064_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4070_, lean_object* v_toBind_4071_, lean_object* v_ctx_x3f_4072_, lean_object* v_inst_4073_, lean_object* v___f_4074_, lean_object* v_st_4075_){
_start:
{
lean_object* v_assignment_4076_; lean_object* v_trees_4077_; lean_object* v___f_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_assignment_4076_ = lean_ctor_get(v_st_4075_, 0);
lean_inc_ref(v_assignment_4076_);
v_trees_4077_ = lean_ctor_get(v_st_4075_, 2);
lean_inc_ref(v_trees_4077_);
lean_dec_ref(v_st_4075_);
lean_inc(v_toBind_4071_);
v___f_4078_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4078_, 0, v_assignment_4076_);
lean_closure_set(v___f_4078_, 1, v_toPure_4070_);
lean_closure_set(v___f_4078_, 2, v_toBind_4071_);
lean_closure_set(v___f_4078_, 3, v_ctx_x3f_4072_);
v___x_4079_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4073_, v___f_4078_, v_trees_4077_);
v___x_4080_ = lean_apply_4(v_toBind_4071_, lean_box(0), lean_box(0), v___x_4079_, v___f_4074_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4081_, lean_object* v_modifyInfoState_4082_, lean_object* v_toBind_4083_, lean_object* v_ctx_x3f_4084_, lean_object* v_inst_4085_, lean_object* v_getInfoState_4086_, lean_object* v_inst_4087_, lean_object* v_x_4088_, lean_object* v___f_4089_, lean_object* v_treesSaved_4090_){
_start:
{
lean_object* v_toFunctor_4091_; lean_object* v_toPure_4092_; lean_object* v_map_4093_; lean_object* v___f_4094_; lean_object* v___f_4095_; lean_object* v___f_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_toFunctor_4091_ = lean_ctor_get(v_toApplicative_4081_, 0);
lean_inc_ref(v_toFunctor_4091_);
v_toPure_4092_ = lean_ctor_get(v_toApplicative_4081_, 1);
lean_inc(v_toPure_4092_);
lean_dec_ref(v_toApplicative_4081_);
v_map_4093_ = lean_ctor_get(v_toFunctor_4091_, 0);
lean_inc(v_map_4093_);
lean_dec_ref(v_toFunctor_4091_);
v___f_4094_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4094_, 0, v_treesSaved_4090_);
lean_closure_set(v___f_4094_, 1, v_modifyInfoState_4082_);
lean_inc(v_toBind_4083_);
v___f_4095_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4095_, 0, v_toPure_4092_);
lean_closure_set(v___f_4095_, 1, v_toBind_4083_);
lean_closure_set(v___f_4095_, 2, v_ctx_x3f_4084_);
lean_closure_set(v___f_4095_, 3, v_inst_4085_);
lean_closure_set(v___f_4095_, 4, v___f_4094_);
v___f_4096_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4096_, 0, v_toBind_4083_);
lean_closure_set(v___f_4096_, 1, v_getInfoState_4086_);
lean_closure_set(v___f_4096_, 2, v___f_4095_);
v___x_4097_ = lean_apply_4(v_inst_4087_, lean_box(0), lean_box(0), v_x_4088_, v___f_4096_);
v___x_4098_ = lean_apply_4(v_map_4093_, lean_box(0), lean_box(0), v___f_4089_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_x_4102_, lean_object* v_ctx_x3f_4103_){
_start:
{
lean_object* v_toApplicative_4104_; lean_object* v_toBind_4105_; lean_object* v_getInfoState_4106_; lean_object* v_modifyInfoState_4107_; lean_object* v___f_4108_; lean_object* v___f_4109_; lean_object* v___f_4110_; lean_object* v___x_4111_; 
v_toApplicative_4104_ = lean_ctor_get(v_inst_4099_, 0);
v_toBind_4105_ = lean_ctor_get(v_inst_4099_, 1);
lean_inc_n(v_toBind_4105_, 3);
v_getInfoState_4106_ = lean_ctor_get(v_inst_4100_, 0);
lean_inc_n(v_getInfoState_4106_, 2);
v_modifyInfoState_4107_ = lean_ctor_get(v_inst_4100_, 1);
v___f_4108_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4102_);
lean_inc_ref(v_inst_4099_);
lean_inc(v_modifyInfoState_4107_);
lean_inc_ref(v_toApplicative_4104_);
v___f_4109_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4109_, 0, v_toApplicative_4104_);
lean_closure_set(v___f_4109_, 1, v_modifyInfoState_4107_);
lean_closure_set(v___f_4109_, 2, v_toBind_4105_);
lean_closure_set(v___f_4109_, 3, v_ctx_x3f_4103_);
lean_closure_set(v___f_4109_, 4, v_inst_4099_);
lean_closure_set(v___f_4109_, 5, v_getInfoState_4106_);
lean_closure_set(v___f_4109_, 6, v_inst_4101_);
lean_closure_set(v___f_4109_, 7, v_x_4102_);
lean_closure_set(v___f_4109_, 8, v___f_4108_);
v___f_4110_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4110_, 0, v_x_4102_);
lean_closure_set(v___f_4110_, 1, v_inst_4099_);
lean_closure_set(v___f_4110_, 2, v_inst_4100_);
lean_closure_set(v___f_4110_, 3, v_toBind_4105_);
lean_closure_set(v___f_4110_, 4, v___f_4109_);
v___x_4111_ = lean_apply_4(v_toBind_4105_, lean_box(0), lean_box(0), v_getInfoState_4106_, v___f_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4112_, lean_object* v_inst_4113_, lean_object* v_inst_4114_, lean_object* v_00_u03b1_4115_, lean_object* v_inst_4116_, lean_object* v_x_4117_, lean_object* v_ctx_x3f_4118_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4113_, v_inst_4114_, v_inst_4116_, v_x_4117_, v_ctx_x3f_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4120_, lean_object* v_____do__lift_4121_){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_____do__lift_4121_);
v___x_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
v___x_4124_ = lean_apply_2(v_toPure_4120_, lean_box(0), v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4125_, lean_object* v_inst_4126_, lean_object* v_inst_4127_, lean_object* v_inst_4128_, lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_inst_4133_, lean_object* v_x_4134_){
_start:
{
lean_object* v_toApplicative_4135_; lean_object* v_toBind_4136_; lean_object* v_toPure_4137_; lean_object* v___x_4138_; lean_object* v___f_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_toApplicative_4135_ = lean_ctor_get(v_inst_4125_, 0);
v_toBind_4136_ = lean_ctor_get(v_inst_4125_, 1);
v_toPure_4137_ = lean_ctor_get(v_toApplicative_4135_, 1);
lean_inc_ref(v_inst_4125_);
v___x_4138_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4125_, v_inst_4129_, v_inst_4131_, v_inst_4130_, v_inst_4132_, v_inst_4127_, v_inst_4133_);
lean_inc(v_toPure_4137_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4139_, 0, v_toPure_4137_);
lean_inc(v_toBind_4136_);
v___x_4140_ = lean_apply_4(v_toBind_4136_, lean_box(0), lean_box(0), v___x_4138_, v___f_4139_);
v___x_4141_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4125_, v_inst_4126_, v_inst_4128_, v_x_4134_, v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4142_, lean_object* v_inst_4143_, lean_object* v_inst_4144_, lean_object* v_00_u03b1_4145_, lean_object* v_inst_4146_, lean_object* v_inst_4147_, lean_object* v_inst_4148_, lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_inst_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4143_, v_inst_4144_, v_inst_4146_, v_inst_4147_, v_inst_4148_, v_inst_4149_, v_inst_4150_, v_inst_4151_, v_inst_4152_, v_x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4155_, lean_object* v_____x_4156_){
_start:
{
if (lean_obj_tag(v_____x_4156_) == 1)
{
lean_object* v_val_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4166_; 
v_val_4157_ = lean_ctor_get(v_____x_4156_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_____x_4156_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4159_ = v_____x_4156_;
v_isShared_4160_ = v_isSharedCheck_4166_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_val_4157_);
lean_dec(v_____x_4156_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4166_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_val_4157_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v___x_4161_);
v___x_4163_ = v___x_4159_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_apply_2(v_toPure_4155_, lean_box(0), v___x_4163_);
return v___x_4164_;
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec(v_____x_4156_);
v___x_4167_ = lean_box(0);
v___x_4168_ = lean_apply_2(v_toPure_4155_, lean_box(0), v___x_4167_);
return v___x_4168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4169_, lean_object* v_inst_4170_, lean_object* v_inst_4171_, lean_object* v_inst_4172_, lean_object* v_x_4173_){
_start:
{
lean_object* v_toApplicative_4174_; lean_object* v_toBind_4175_; lean_object* v_toPure_4176_; lean_object* v___f_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_toApplicative_4174_ = lean_ctor_get(v_inst_4169_, 0);
v_toBind_4175_ = lean_ctor_get(v_inst_4169_, 1);
v_toPure_4176_ = lean_ctor_get(v_toApplicative_4174_, 1);
lean_inc(v_toPure_4176_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4177_, 0, v_toPure_4176_);
lean_inc(v_toBind_4175_);
v___x_4178_ = lean_apply_4(v_toBind_4175_, lean_box(0), lean_box(0), v_inst_4172_, v___f_4177_);
v___x_4179_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4169_, v_inst_4170_, v_inst_4171_, v_x_4173_, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_00_u03b1_4183_, lean_object* v_inst_4184_, lean_object* v_inst_4185_, lean_object* v_x_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4181_, v_inst_4182_, v_inst_4184_, v_inst_4185_, v_x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4188_, lean_object* v_autoImplicits_4189_){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4190_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_autoImplicits_4189_);
v___x_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
v___x_4192_ = lean_apply_2(v_toPure_4188_, lean_box(0), v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v_toApplicative_4198_; lean_object* v_toBind_4199_; lean_object* v_toPure_4200_; lean_object* v___f_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_toApplicative_4198_ = lean_ctor_get(v_inst_4193_, 0);
v_toBind_4199_ = lean_ctor_get(v_inst_4193_, 1);
v_toPure_4200_ = lean_ctor_get(v_toApplicative_4198_, 1);
lean_inc(v_toPure_4200_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4201_, 0, v_toPure_4200_);
lean_inc(v_toBind_4199_);
v___x_4202_ = lean_apply_4(v_toBind_4199_, lean_box(0), lean_box(0), v_inst_4196_, v___f_4201_);
v___x_4203_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4193_, v_inst_4194_, v_inst_4195_, v_x_4197_, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4204_, lean_object* v_inst_4205_, lean_object* v_inst_4206_, lean_object* v_00_u03b1_4207_, lean_object* v_inst_4208_, lean_object* v_inst_4209_, lean_object* v_x_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4205_, v_inst_4206_, v_inst_4208_, v_inst_4209_, v_x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v_mvarId_4214_, lean_object* v_toPure_4215_, lean_object* v_____do__lift_4216_){
_start:
{
lean_object* v_assignment_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_assignment_4217_ = lean_ctor_get(v_____do__lift_4216_, 0);
v___x_4218_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4212_, v___x_4213_, v_assignment_4217_, v_mvarId_4214_);
v___x_4219_ = lean_apply_2(v_toPure_4215_, lean_box(0), v___x_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_4220_, lean_object* v___x_4221_, lean_object* v_mvarId_4222_, lean_object* v_toPure_4223_, lean_object* v_____do__lift_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_4220_, v___x_4221_, v_mvarId_4222_, v_toPure_4223_, v_____do__lift_4224_);
lean_dec_ref(v_____do__lift_4224_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4228_, lean_object* v_inst_4229_, lean_object* v_mvarId_4230_){
_start:
{
lean_object* v_toApplicative_4231_; lean_object* v_toBind_4232_; lean_object* v_getInfoState_4233_; lean_object* v_toPure_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; 
v_toApplicative_4231_ = lean_ctor_get(v_inst_4228_, 0);
lean_inc_ref(v_toApplicative_4231_);
v_toBind_4232_ = lean_ctor_get(v_inst_4228_, 1);
lean_inc(v_toBind_4232_);
lean_dec_ref(v_inst_4228_);
v_getInfoState_4233_ = lean_ctor_get(v_inst_4229_, 0);
lean_inc(v_getInfoState_4233_);
lean_dec_ref(v_inst_4229_);
v_toPure_4234_ = lean_ctor_get(v_toApplicative_4231_, 1);
lean_inc(v_toPure_4234_);
lean_dec_ref(v_toApplicative_4231_);
v___x_4235_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4236_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4237_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4237_, 0, v___x_4235_);
lean_closure_set(v___f_4237_, 1, v___x_4236_);
lean_closure_set(v___f_4237_, 2, v_mvarId_4230_);
lean_closure_set(v___f_4237_, 3, v_toPure_4234_);
v___x_4238_ = lean_apply_4(v_toBind_4232_, lean_box(0), lean_box(0), v_getInfoState_4233_, v___f_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4239_, lean_object* v_inst_4240_, lean_object* v_inst_4241_, lean_object* v_mvarId_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4240_, v_inst_4241_, v_mvarId_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4244_, lean_object* v_infoTree_4245_, lean_object* v_s_4246_){
_start:
{
uint8_t v_enabled_4247_; lean_object* v_assignment_4248_; lean_object* v_lazyAssignment_4249_; lean_object* v_trees_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4260_; 
v_enabled_4247_ = lean_ctor_get_uint8(v_s_4246_, sizeof(void*)*3);
v_assignment_4248_ = lean_ctor_get(v_s_4246_, 0);
v_lazyAssignment_4249_ = lean_ctor_get(v_s_4246_, 1);
v_trees_4250_ = lean_ctor_get(v_s_4246_, 2);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_s_4246_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4252_ = v_s_4246_;
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_trees_4250_);
lean_inc(v_lazyAssignment_4249_);
lean_inc(v_assignment_4248_);
lean_dec(v_s_4246_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4254_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4255_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4256_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4254_, v___x_4255_, v_assignment_4248_, v_mvarId_4244_, v_infoTree_4245_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4256_);
v___x_4258_ = v___x_4252_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_lazyAssignment_4249_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_trees_4250_);
lean_ctor_set_uint8(v_reuseFailAlloc_4259_, sizeof(void*)*3, v_enabled_4247_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4263_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4264_ = lean_unsigned_to_nat(2u);
v___x_4265_ = lean_unsigned_to_nat(491u);
v___x_4266_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4267_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4268_ = l_mkPanicMessageWithDecl(v___x_4267_, v___x_4266_, v___x_4265_, v___x_4264_, v___x_4263_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4269_, lean_object* v___f_4270_, lean_object* v_inst_4271_, lean_object* v_____do__lift_4272_){
_start:
{
if (lean_obj_tag(v_____do__lift_4272_) == 0)
{
lean_object* v_modifyInfoState_4273_; lean_object* v___x_4274_; 
lean_dec_ref(v_inst_4271_);
v_modifyInfoState_4273_ = lean_ctor_get(v_inst_4269_, 1);
lean_inc(v_modifyInfoState_4273_);
lean_dec_ref(v_inst_4269_);
v___x_4274_ = lean_apply_1(v_modifyInfoState_4273_, v___f_4270_);
return v___x_4274_;
}
else
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
lean_dec_ref(v___f_4270_);
lean_dec_ref(v_inst_4269_);
v___x_4275_ = lean_box(0);
v___x_4276_ = l_instInhabitedOfMonad___redArg(v_inst_4271_, v___x_4275_);
v___x_4277_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4278_ = l_panic___redArg(v___x_4276_, v___x_4277_);
lean_dec(v___x_4276_);
return v___x_4278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4279_, lean_object* v___f_4280_, lean_object* v_inst_4281_, lean_object* v_____do__lift_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4279_, v___f_4280_, v_inst_4281_, v_____do__lift_4282_);
lean_dec(v_____do__lift_4282_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4284_, lean_object* v_inst_4285_, lean_object* v_mvarId_4286_, lean_object* v_infoTree_4287_){
_start:
{
lean_object* v_toBind_4288_; lean_object* v___f_4289_; lean_object* v___f_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_toBind_4288_ = lean_ctor_get(v_inst_4284_, 1);
lean_inc(v_toBind_4288_);
lean_inc(v_mvarId_4286_);
v___f_4289_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4289_, 0, v_mvarId_4286_);
lean_closure_set(v___f_4289_, 1, v_infoTree_4287_);
lean_inc_ref(v_inst_4284_);
lean_inc_ref(v_inst_4285_);
v___f_4290_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4290_, 0, v_inst_4285_);
lean_closure_set(v___f_4290_, 1, v___f_4289_);
lean_closure_set(v___f_4290_, 2, v_inst_4284_);
v___x_4291_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4284_, v_inst_4285_, v_mvarId_4286_);
v___x_4292_ = lean_apply_4(v_toBind_4288_, lean_box(0), lean_box(0), v___x_4291_, v___f_4290_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4293_, lean_object* v_inst_4294_, lean_object* v_inst_4295_, lean_object* v_mvarId_4296_, lean_object* v_infoTree_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4294_, v_inst_4295_, v_mvarId_4296_, v_infoTree_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4299_, lean_object* v_output_4300_, lean_object* v_toPure_4301_, lean_object* v_____do__lift_4302_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4303_, 0, v_____do__lift_4302_);
lean_ctor_set(v___x_4303_, 1, v_stx_4299_);
lean_ctor_set(v___x_4303_, 2, v_output_4300_);
v___x_4304_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
v___x_4305_ = lean_apply_2(v_toPure_4301_, lean_box(0), v___x_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4306_, lean_object* v_inst_4307_, lean_object* v_inst_4308_, lean_object* v_inst_4309_, lean_object* v_stx_4310_, lean_object* v_output_4311_, lean_object* v_x_4312_){
_start:
{
lean_object* v_toApplicative_4313_; lean_object* v_toBind_4314_; lean_object* v_toPure_4315_; lean_object* v___f_4316_; lean_object* v_mkInfo_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; 
v_toApplicative_4313_ = lean_ctor_get(v_inst_4307_, 0);
v_toBind_4314_ = lean_ctor_get(v_inst_4307_, 1);
v_toPure_4315_ = lean_ctor_get(v_toApplicative_4313_, 1);
lean_inc_n(v_toPure_4315_, 2);
v___f_4316_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4316_, 0, v_stx_4310_);
lean_closure_set(v___f_4316_, 1, v_output_4311_);
lean_closure_set(v___f_4316_, 2, v_toPure_4315_);
lean_inc_n(v_toBind_4314_, 2);
v_mkInfo_4317_ = lean_apply_4(v_toBind_4314_, lean_box(0), lean_box(0), v_inst_4309_, v___f_4316_);
v___f_4318_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4318_, 0, v_toPure_4315_);
lean_closure_set(v___f_4318_, 1, v_toBind_4314_);
lean_closure_set(v___f_4318_, 2, v_mkInfo_4317_);
v___x_4319_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4307_, v_inst_4308_, v_inst_4306_, v_x_4312_, v___f_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4320_, lean_object* v_00_u03b1_4321_, lean_object* v_inst_4322_, lean_object* v_inst_4323_, lean_object* v_inst_4324_, lean_object* v_inst_4325_, lean_object* v_stx_4326_, lean_object* v_output_4327_, lean_object* v_x_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4322_, v_inst_4323_, v_inst_4324_, v_inst_4325_, v_stx_4326_, v_output_4327_, v_x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4330_, lean_object* v_mvarId_4331_, lean_object* v_s_4332_){
_start:
{
lean_object* v_trees_4333_; uint8_t v_enabled_4334_; lean_object* v_assignment_4335_; lean_object* v_lazyAssignment_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4356_; 
v_trees_4333_ = lean_ctor_get(v_s_4332_, 2);
v_enabled_4334_ = lean_ctor_get_uint8(v_s_4332_, sizeof(void*)*3);
v_assignment_4335_ = lean_ctor_get(v_s_4332_, 0);
v_lazyAssignment_4336_ = lean_ctor_get(v_s_4332_, 1);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_s_4332_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4338_ = v_s_4332_;
v_isShared_4339_ = v_isSharedCheck_4356_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_trees_4333_);
lean_inc(v_lazyAssignment_4336_);
lean_inc(v_assignment_4335_);
lean_dec(v_s_4332_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4356_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_size_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_size_4340_ = lean_ctor_get(v_trees_4333_, 2);
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = lean_nat_dec_lt(v___x_4341_, v_size_4340_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4344_; 
lean_dec_ref(v_trees_4333_);
lean_dec(v_mvarId_4331_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 2, v_treesSaved_4330_);
v___x_4344_ = v___x_4338_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_assignment_4335_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_lazyAssignment_4336_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v_treesSaved_4330_);
lean_ctor_set_uint8(v_reuseFailAlloc_4345_, sizeof(void*)*3, v_enabled_4334_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4346_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4347_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4348_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4349_ = lean_unsigned_to_nat(1u);
v___x_4350_ = lean_nat_sub(v_size_4340_, v___x_4349_);
v___x_4351_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4348_, v_trees_4333_, v___x_4350_);
lean_dec(v___x_4350_);
lean_dec_ref(v_trees_4333_);
v___x_4352_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4346_, v___x_4347_, v_assignment_4335_, v_mvarId_4331_, v___x_4351_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 2, v_treesSaved_4330_);
lean_ctor_set(v___x_4338_, 0, v___x_4352_);
v___x_4354_ = v___x_4338_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_lazyAssignment_4336_);
lean_ctor_set(v_reuseFailAlloc_4355_, 2, v_treesSaved_4330_);
lean_ctor_set_uint8(v_reuseFailAlloc_4355_, sizeof(void*)*3, v_enabled_4334_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4357_, lean_object* v___f_4358_, lean_object* v_x_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_apply_1(v_modifyInfoState_4357_, v___f_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4361_, lean_object* v___f_4362_, lean_object* v_x_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4361_, v___f_4362_, v_x_4363_);
lean_dec(v_x_4363_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4365_, lean_object* v_mvarId_4366_, lean_object* v_modifyInfoState_4367_, lean_object* v_inst_4368_, lean_object* v_x_4369_, lean_object* v___f_4370_, lean_object* v_treesSaved_4371_){
_start:
{
lean_object* v_toFunctor_4372_; lean_object* v_map_4373_; lean_object* v___f_4374_; lean_object* v___f_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_toFunctor_4372_ = lean_ctor_get(v_toApplicative_4365_, 0);
lean_inc_ref(v_toFunctor_4372_);
lean_dec_ref(v_toApplicative_4365_);
v_map_4373_ = lean_ctor_get(v_toFunctor_4372_, 0);
lean_inc(v_map_4373_);
lean_dec_ref(v_toFunctor_4372_);
v___f_4374_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4374_, 0, v_treesSaved_4371_);
lean_closure_set(v___f_4374_, 1, v_mvarId_4366_);
v___f_4375_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4375_, 0, v_modifyInfoState_4367_);
lean_closure_set(v___f_4375_, 1, v___f_4374_);
v___x_4376_ = lean_apply_4(v_inst_4368_, lean_box(0), lean_box(0), v_x_4369_, v___f_4375_);
v___x_4377_ = lean_apply_4(v_map_4373_, lean_box(0), lean_box(0), v___f_4370_, v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_inst_4380_, lean_object* v_mvarId_4381_, lean_object* v_x_4382_){
_start:
{
lean_object* v_toApplicative_4383_; lean_object* v_toBind_4384_; lean_object* v_getInfoState_4385_; lean_object* v_modifyInfoState_4386_; lean_object* v___f_4387_; lean_object* v___f_4388_; lean_object* v___f_4389_; lean_object* v___x_4390_; 
v_toApplicative_4383_ = lean_ctor_get(v_inst_4379_, 0);
v_toBind_4384_ = lean_ctor_get(v_inst_4379_, 1);
lean_inc_n(v_toBind_4384_, 2);
v_getInfoState_4385_ = lean_ctor_get(v_inst_4380_, 0);
lean_inc(v_getInfoState_4385_);
v_modifyInfoState_4386_ = lean_ctor_get(v_inst_4380_, 1);
v___f_4387_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4382_);
lean_inc(v_modifyInfoState_4386_);
lean_inc_ref(v_toApplicative_4383_);
v___f_4388_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4388_, 0, v_toApplicative_4383_);
lean_closure_set(v___f_4388_, 1, v_mvarId_4381_);
lean_closure_set(v___f_4388_, 2, v_modifyInfoState_4386_);
lean_closure_set(v___f_4388_, 3, v_inst_4378_);
lean_closure_set(v___f_4388_, 4, v_x_4382_);
lean_closure_set(v___f_4388_, 5, v___f_4387_);
v___f_4389_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4389_, 0, v_x_4382_);
lean_closure_set(v___f_4389_, 1, v_inst_4379_);
lean_closure_set(v___f_4389_, 2, v_inst_4380_);
lean_closure_set(v___f_4389_, 3, v_toBind_4384_);
lean_closure_set(v___f_4389_, 4, v___f_4388_);
v___x_4390_ = lean_apply_4(v_toBind_4384_, lean_box(0), lean_box(0), v_getInfoState_4385_, v___f_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4391_, lean_object* v_00_u03b1_4392_, lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_inst_4395_, lean_object* v_mvarId_4396_, lean_object* v_x_4397_){
_start:
{
lean_object* v_toApplicative_4398_; lean_object* v_toBind_4399_; lean_object* v_getInfoState_4400_; lean_object* v_modifyInfoState_4401_; lean_object* v___f_4402_; lean_object* v___f_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; 
v_toApplicative_4398_ = lean_ctor_get(v_inst_4394_, 0);
v_toBind_4399_ = lean_ctor_get(v_inst_4394_, 1);
lean_inc_n(v_toBind_4399_, 2);
v_getInfoState_4400_ = lean_ctor_get(v_inst_4395_, 0);
lean_inc(v_getInfoState_4400_);
v_modifyInfoState_4401_ = lean_ctor_get(v_inst_4395_, 1);
v___f_4402_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4397_);
lean_inc(v_modifyInfoState_4401_);
lean_inc_ref(v_toApplicative_4398_);
v___f_4403_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4403_, 0, v_toApplicative_4398_);
lean_closure_set(v___f_4403_, 1, v_mvarId_4396_);
lean_closure_set(v___f_4403_, 2, v_modifyInfoState_4401_);
lean_closure_set(v___f_4403_, 3, v_inst_4393_);
lean_closure_set(v___f_4403_, 4, v_x_4397_);
lean_closure_set(v___f_4403_, 5, v___f_4402_);
v___f_4404_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4404_, 0, v_x_4397_);
lean_closure_set(v___f_4404_, 1, v_inst_4394_);
lean_closure_set(v___f_4404_, 2, v_inst_4395_);
lean_closure_set(v___f_4404_, 3, v_toBind_4399_);
lean_closure_set(v___f_4404_, 4, v___f_4403_);
v___x_4405_ = lean_apply_4(v_toBind_4399_, lean_box(0), lean_box(0), v_getInfoState_4400_, v___f_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4406_, lean_object* v_s_4407_){
_start:
{
lean_object* v_assignment_4408_; lean_object* v_lazyAssignment_4409_; lean_object* v_trees_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
v_assignment_4408_ = lean_ctor_get(v_s_4407_, 0);
v_lazyAssignment_4409_ = lean_ctor_get(v_s_4407_, 1);
v_trees_4410_ = lean_ctor_get(v_s_4407_, 2);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_s_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v_s_4407_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_trees_4410_);
lean_inc(v_lazyAssignment_4409_);
lean_inc(v_assignment_4408_);
lean_dec(v_s_4407_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_assignment_4408_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_lazyAssignment_4409_);
lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_trees_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*3, v_flag_4406_);
return v___x_4415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4418_, lean_object* v_s_4419_){
_start:
{
uint8_t v_flag_boxed_4420_; lean_object* v_res_4421_; 
v_flag_boxed_4420_ = lean_unbox(v_flag_4418_);
v_res_4421_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4420_, v_s_4419_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4422_, uint8_t v_flag_4423_){
_start:
{
lean_object* v_modifyInfoState_4424_; lean_object* v___x_4425_; lean_object* v___f_4426_; lean_object* v___x_4427_; 
v_modifyInfoState_4424_ = lean_ctor_get(v_inst_4422_, 1);
lean_inc(v_modifyInfoState_4424_);
lean_dec_ref(v_inst_4422_);
v___x_4425_ = lean_box(v_flag_4423_);
v___f_4426_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4426_, 0, v___x_4425_);
v___x_4427_ = lean_apply_1(v_modifyInfoState_4424_, v___f_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4428_, lean_object* v_flag_4429_){
_start:
{
uint8_t v_flag_boxed_4430_; lean_object* v_res_4431_; 
v_flag_boxed_4430_ = lean_unbox(v_flag_4429_);
v_res_4431_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4428_, v_flag_boxed_4430_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4432_, lean_object* v_inst_4433_, uint8_t v_flag_4434_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4433_, v_flag_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4436_, lean_object* v_inst_4437_, lean_object* v_flag_4438_){
_start:
{
uint8_t v_flag_boxed_4439_; lean_object* v_res_4440_; 
v_flag_boxed_4439_ = lean_unbox(v_flag_4438_);
v_res_4440_ = l_Lean_Elab_enableInfoTree(v_m_4436_, v_inst_4437_, v_flag_boxed_4439_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4441_){
_start:
{
lean_object* v_fst_4442_; 
v_fst_4442_ = lean_ctor_get(v_x_4441_, 0);
lean_inc(v_fst_4442_);
return v_fst_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4443_);
lean_dec_ref(v_x_4443_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4445_, lean_object* v_____r_4446_){
_start:
{
lean_inc(v_x_4445_);
return v_x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4447_, lean_object* v_____r_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4447_, v_____r_4448_);
lean_dec(v_x_4447_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4450_, lean_object* v_x_4451_){
_start:
{
lean_inc(v___x_4450_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4452_, lean_object* v_x_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4452_, v_x_4453_);
lean_dec(v_x_4453_);
lean_dec(v___x_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4455_, lean_object* v_inst_4456_, uint8_t v_flag_4457_, lean_object* v_toBind_4458_, lean_object* v___f_4459_, lean_object* v_inst_4460_, lean_object* v___f_4461_, lean_object* v_____do__lift_4462_){
_start:
{
uint8_t v_enabled_4463_; lean_object* v_map_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___f_4468_; lean_object* v_y_4469_; lean_object* v___x_4470_; 
v_enabled_4463_ = lean_ctor_get_uint8(v_____do__lift_4462_, sizeof(void*)*3);
v_map_4464_ = lean_ctor_get(v_toFunctor_4455_, 0);
lean_inc(v_map_4464_);
lean_dec_ref(v_toFunctor_4455_);
lean_inc_ref(v_inst_4456_);
v___x_4465_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4456_, v_flag_4457_);
v___x_4466_ = lean_apply_4(v_toBind_4458_, lean_box(0), lean_box(0), v___x_4465_, v___f_4459_);
v___x_4467_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4456_, v_enabled_4463_);
v___f_4468_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4468_, 0, v___x_4467_);
v_y_4469_ = lean_apply_4(v_inst_4460_, lean_box(0), lean_box(0), v___x_4466_, v___f_4468_);
v___x_4470_ = lean_apply_4(v_map_4464_, lean_box(0), lean_box(0), v___f_4461_, v_y_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4471_, lean_object* v_inst_4472_, lean_object* v_flag_4473_, lean_object* v_toBind_4474_, lean_object* v___f_4475_, lean_object* v_inst_4476_, lean_object* v___f_4477_, lean_object* v_____do__lift_4478_){
_start:
{
uint8_t v_flag_boxed_4479_; lean_object* v_res_4480_; 
v_flag_boxed_4479_ = lean_unbox(v_flag_4473_);
v_res_4480_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4471_, v_inst_4472_, v_flag_boxed_4479_, v_toBind_4474_, v___f_4475_, v_inst_4476_, v___f_4477_, v_____do__lift_4478_);
lean_dec_ref(v_____do__lift_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4482_, lean_object* v_inst_4483_, lean_object* v_inst_4484_, uint8_t v_flag_4485_, lean_object* v_x_4486_){
_start:
{
lean_object* v_toApplicative_4487_; lean_object* v_toBind_4488_; lean_object* v_getInfoState_4489_; lean_object* v_toFunctor_4490_; lean_object* v___f_4491_; lean_object* v___f_4492_; lean_object* v___x_4493_; lean_object* v___f_4494_; lean_object* v___x_4495_; 
v_toApplicative_4487_ = lean_ctor_get(v_inst_4482_, 0);
lean_inc_ref(v_toApplicative_4487_);
v_toBind_4488_ = lean_ctor_get(v_inst_4482_, 1);
lean_inc_n(v_toBind_4488_, 2);
lean_dec_ref(v_inst_4482_);
v_getInfoState_4489_ = lean_ctor_get(v_inst_4483_, 0);
lean_inc(v_getInfoState_4489_);
v_toFunctor_4490_ = lean_ctor_get(v_toApplicative_4487_, 0);
lean_inc_ref(v_toFunctor_4490_);
lean_dec_ref(v_toApplicative_4487_);
v___f_4491_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4492_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4492_, 0, v_x_4486_);
v___x_4493_ = lean_box(v_flag_4485_);
v___f_4494_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4494_, 0, v_toFunctor_4490_);
lean_closure_set(v___f_4494_, 1, v_inst_4483_);
lean_closure_set(v___f_4494_, 2, v___x_4493_);
lean_closure_set(v___f_4494_, 3, v_toBind_4488_);
lean_closure_set(v___f_4494_, 4, v___f_4492_);
lean_closure_set(v___f_4494_, 5, v_inst_4484_);
lean_closure_set(v___f_4494_, 6, v___f_4491_);
v___x_4495_ = lean_apply_4(v_toBind_4488_, lean_box(0), lean_box(0), v_getInfoState_4489_, v___f_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4496_, lean_object* v_inst_4497_, lean_object* v_inst_4498_, lean_object* v_flag_4499_, lean_object* v_x_4500_){
_start:
{
uint8_t v_flag_boxed_4501_; lean_object* v_res_4502_; 
v_flag_boxed_4501_ = lean_unbox(v_flag_4499_);
v_res_4502_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4496_, v_inst_4497_, v_inst_4498_, v_flag_boxed_4501_, v_x_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4503_, lean_object* v_00_u03b1_4504_, lean_object* v_inst_4505_, lean_object* v_inst_4506_, lean_object* v_inst_4507_, uint8_t v_flag_4508_, lean_object* v_x_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4505_, v_inst_4506_, v_inst_4507_, v_flag_4508_, v_x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4511_, lean_object* v_00_u03b1_4512_, lean_object* v_inst_4513_, lean_object* v_inst_4514_, lean_object* v_inst_4515_, lean_object* v_flag_4516_, lean_object* v_x_4517_){
_start:
{
uint8_t v_flag_boxed_4518_; lean_object* v_res_4519_; 
v_flag_boxed_4518_ = lean_unbox(v_flag_4516_);
v_res_4519_ = l_Lean_Elab_withEnableInfoTree(v_m_4511_, v_00_u03b1_4512_, v_inst_4513_, v_inst_4514_, v_inst_4515_, v_flag_boxed_4518_, v_x_4517_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4520_, lean_object* v_____do__lift_4521_){
_start:
{
lean_object* v_trees_4522_; lean_object* v___x_4523_; 
v_trees_4522_ = lean_ctor_get(v_____do__lift_4521_, 2);
lean_inc_ref(v_trees_4522_);
lean_dec_ref(v_____do__lift_4521_);
v___x_4523_ = lean_apply_2(v_toPure_4520_, lean_box(0), v_trees_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4524_, lean_object* v_inst_4525_){
_start:
{
lean_object* v_toApplicative_4526_; lean_object* v_toBind_4527_; lean_object* v_getInfoState_4528_; lean_object* v_toPure_4529_; lean_object* v___f_4530_; lean_object* v___x_4531_; 
v_toApplicative_4526_ = lean_ctor_get(v_inst_4525_, 0);
lean_inc_ref(v_toApplicative_4526_);
v_toBind_4527_ = lean_ctor_get(v_inst_4525_, 1);
lean_inc(v_toBind_4527_);
lean_dec_ref(v_inst_4525_);
v_getInfoState_4528_ = lean_ctor_get(v_inst_4524_, 0);
lean_inc(v_getInfoState_4528_);
lean_dec_ref(v_inst_4524_);
v_toPure_4529_ = lean_ctor_get(v_toApplicative_4526_, 1);
lean_inc(v_toPure_4529_);
lean_dec_ref(v_toApplicative_4526_);
v___f_4530_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4530_, 0, v_toPure_4529_);
v___x_4531_ = lean_apply_4(v_toBind_4527_, lean_box(0), lean_box(0), v_getInfoState_4528_, v___f_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4532_, lean_object* v_inst_4533_, lean_object* v_inst_4534_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4533_, v_inst_4534_);
return v___x_4535_;
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
