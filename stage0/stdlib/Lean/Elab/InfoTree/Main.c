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
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_toCommandContextInfo_1148_; lean_object* v_env_1149_; lean_object* v_options_1150_; lean_object* v_currNamespace_1151_; lean_object* v_openDecls_1152_; lean_object* v_ngen_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___y_1166_; lean_object* v___y_1167_; lean_object* v_fileName_1168_; lean_object* v_fileMap_1169_; lean_object* v_currRecDepth_1170_; lean_object* v_ref_1171_; lean_object* v_currNamespace_1172_; lean_object* v_openDecls_1173_; lean_object* v_initHeartbeats_1174_; lean_object* v_maxHeartbeats_1175_; lean_object* v_quotContext_1176_; lean_object* v_currMacroScope_1177_; lean_object* v_cancelTk_x3f_1178_; uint8_t v_suppressElabErrors_1179_; lean_object* v_inheritedTraceOptions_1180_; lean_object* v___y_1181_; uint8_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; uint8_t v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_env_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1303_; uint8_t v___x_1324_; 
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
v___x_1163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1163_, 0, v_env_1157_);
lean_ctor_set(v___x_1163_, 1, v___x_1155_);
lean_ctor_set(v___x_1163_, 2, v_ngen_1153_);
lean_ctor_set(v___x_1163_, 3, v___x_1159_);
lean_ctor_set(v___x_1163_, 4, v___x_1160_);
lean_ctor_set(v___x_1163_, 5, v___x_1145_);
lean_ctor_set(v___x_1163_, 6, v___x_1146_);
lean_ctor_set(v___x_1163_, 7, v___x_1161_);
lean_ctor_set(v___x_1163_, 8, v___x_1162_);
lean_ctor_set(v___x_1163_, 9, v___x_1162_);
v___x_1164_ = lean_st_mk_ref(v___x_1163_);
v___x_1257_ = l_Lean_inheritedTraceOptions;
v___x_1258_ = lean_st_ref_get(v___x_1257_);
v___x_1259_ = lean_st_ref_get(v___x_1164_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_1261_ = l_Lean_instInhabitedFileMap_default;
v___x_1262_ = l_Lean_Options_empty;
v___x_1263_ = lean_unsigned_to_nat(1000u);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1267_, 0, v___x_1260_);
lean_ctor_set(v___x_1267_, 1, v___x_1261_);
lean_ctor_set(v___x_1267_, 2, v___x_1262_);
lean_ctor_set(v___x_1267_, 3, v___x_1144_);
lean_ctor_set(v___x_1267_, 4, v___x_1263_);
lean_ctor_set(v___x_1267_, 5, v___x_1264_);
lean_ctor_set(v___x_1267_, 6, v_currNamespace_1151_);
lean_ctor_set(v___x_1267_, 7, v_openDecls_1152_);
lean_ctor_set(v___x_1267_, 8, v___x_1147_);
lean_ctor_set(v___x_1267_, 9, v___x_1265_);
lean_ctor_set(v___x_1267_, 10, v___x_1158_);
lean_ctor_set(v___x_1267_, 11, v___x_1154_);
lean_ctor_set(v___x_1267_, 12, v___x_1266_);
lean_ctor_set(v___x_1267_, 13, v___x_1258_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*14, v___x_1156_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*14 + 1, v___x_1156_);
v_env_1268_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1268_);
lean_dec(v___x_1259_);
v___x_1269_ = l_Lean_diagnostics;
v___x_1270_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_1324_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1268_);
lean_dec_ref(v_env_1268_);
if (v___x_1324_ == 0)
{
if (v___x_1270_ == 0)
{
lean_inc(v___x_1164_);
v___y_1272_ = v___x_1267_;
v___y_1273_ = v___x_1164_;
goto v___jp_1271_;
}
else
{
v___y_1303_ = v___x_1324_;
goto v___jp_1302_;
}
}
else
{
v___y_1303_ = v___x_1270_;
goto v___jp_1302_;
}
v___jp_1165_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_1150_, v___y_1167_);
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
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14, v___y_1166_);
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
lean_object* v___x_1237_; lean_object* v_env_1238_; lean_object* v_nextMacroScope_1239_; lean_object* v_ngen_1240_; lean_object* v_auxDeclNGen_1241_; lean_object* v_traceState_1242_; lean_object* v_messages_1243_; lean_object* v_infoState_1244_; lean_object* v_snapshotTasks_1245_; lean_object* v_newDecls_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1255_; 
v___x_1237_ = lean_st_ref_take(v___y_1234_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
v_nextMacroScope_1239_ = lean_ctor_get(v___x_1237_, 1);
v_ngen_1240_ = lean_ctor_get(v___x_1237_, 2);
v_auxDeclNGen_1241_ = lean_ctor_get(v___x_1237_, 3);
v_traceState_1242_ = lean_ctor_get(v___x_1237_, 4);
v_messages_1243_ = lean_ctor_get(v___x_1237_, 6);
v_infoState_1244_ = lean_ctor_get(v___x_1237_, 7);
v_snapshotTasks_1245_ = lean_ctor_get(v___x_1237_, 8);
v_newDecls_1246_ = lean_ctor_get(v___x_1237_, 9);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1237_, 5);
lean_dec(v_unused_1256_);
v___x_1248_ = v___x_1237_;
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_newDecls_1246_);
lean_inc(v_snapshotTasks_1245_);
lean_inc(v_infoState_1244_);
lean_inc(v_messages_1243_);
lean_inc(v_traceState_1242_);
lean_inc(v_auxDeclNGen_1241_);
lean_inc(v_ngen_1240_);
lean_inc(v_nextMacroScope_1239_);
lean_inc(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = l_Lean_Kernel_enableDiag(v_env_1238_, v___y_1232_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 5, v___x_1145_);
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_nextMacroScope_1239_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_ngen_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_auxDeclNGen_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_traceState_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1254_, 6, v_messages_1243_);
lean_ctor_set(v_reuseFailAlloc_1254_, 7, v_infoState_1244_);
lean_ctor_set(v_reuseFailAlloc_1254_, 8, v_snapshotTasks_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 9, v_newDecls_1246_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_st_ref_set(v___y_1234_, v___x_1252_);
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1234_;
goto v___jp_1213_;
}
}
}
else
{
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1234_;
goto v___jp_1213_;
}
}
v___jp_1271_:
{
lean_object* v___x_1274_; lean_object* v_fileName_1275_; lean_object* v_fileMap_1276_; lean_object* v_currRecDepth_1277_; lean_object* v_ref_1278_; lean_object* v_currNamespace_1279_; lean_object* v_openDecls_1280_; lean_object* v_initHeartbeats_1281_; lean_object* v_maxHeartbeats_1282_; lean_object* v_quotContext_1283_; lean_object* v_currMacroScope_1284_; lean_object* v_cancelTk_x3f_1285_; uint8_t v_suppressElabErrors_1286_; lean_object* v_inheritedTraceOptions_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1299_; 
v___x_1274_ = lean_st_ref_get(v___y_1273_);
v_fileName_1275_ = lean_ctor_get(v___y_1272_, 0);
v_fileMap_1276_ = lean_ctor_get(v___y_1272_, 1);
v_currRecDepth_1277_ = lean_ctor_get(v___y_1272_, 3);
v_ref_1278_ = lean_ctor_get(v___y_1272_, 5);
v_currNamespace_1279_ = lean_ctor_get(v___y_1272_, 6);
v_openDecls_1280_ = lean_ctor_get(v___y_1272_, 7);
v_initHeartbeats_1281_ = lean_ctor_get(v___y_1272_, 8);
v_maxHeartbeats_1282_ = lean_ctor_get(v___y_1272_, 9);
v_quotContext_1283_ = lean_ctor_get(v___y_1272_, 10);
v_currMacroScope_1284_ = lean_ctor_get(v___y_1272_, 11);
v_cancelTk_x3f_1285_ = lean_ctor_get(v___y_1272_, 12);
v_suppressElabErrors_1286_ = lean_ctor_get_uint8(v___y_1272_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1287_ = lean_ctor_get(v___y_1272_, 13);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___y_1272_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; lean_object* v_unused_1301_; 
v_unused_1300_ = lean_ctor_get(v___y_1272_, 4);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v___y_1272_, 2);
lean_dec(v_unused_1301_);
v___x_1289_ = v___y_1272_;
v_isShared_1290_ = v_isSharedCheck_1299_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_inheritedTraceOptions_1287_);
lean_inc(v_cancelTk_x3f_1285_);
lean_inc(v_currMacroScope_1284_);
lean_inc(v_quotContext_1283_);
lean_inc(v_maxHeartbeats_1282_);
lean_inc(v_initHeartbeats_1281_);
lean_inc(v_openDecls_1280_);
lean_inc(v_currNamespace_1279_);
lean_inc(v_ref_1278_);
lean_inc(v_currRecDepth_1277_);
lean_inc(v_fileMap_1276_);
lean_inc(v_fileName_1275_);
lean_dec(v___y_1272_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1299_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_env_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v_env_1291_ = lean_ctor_get(v___x_1274_, 0);
lean_inc_ref(v_env_1291_);
lean_dec(v___x_1274_);
v___x_1292_ = l_Lean_maxRecDepth;
v___x_1293_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
lean_inc_ref(v_inheritedTraceOptions_1287_);
lean_inc(v_cancelTk_x3f_1285_);
lean_inc(v_currMacroScope_1284_);
lean_inc(v_quotContext_1283_);
lean_inc(v_maxHeartbeats_1282_);
lean_inc(v_initHeartbeats_1281_);
lean_inc(v_openDecls_1280_);
lean_inc(v_currNamespace_1279_);
lean_inc(v_ref_1278_);
lean_inc(v_currRecDepth_1277_);
lean_inc_ref(v_fileMap_1276_);
lean_inc_ref(v_fileName_1275_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 4, v___x_1293_);
lean_ctor_set(v___x_1289_, 2, v___x_1262_);
v___x_1295_ = v___x_1289_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_fileName_1275_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_fileMap_1276_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_currRecDepth_1277_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1298_, 5, v_ref_1278_);
lean_ctor_set(v_reuseFailAlloc_1298_, 6, v_currNamespace_1279_);
lean_ctor_set(v_reuseFailAlloc_1298_, 7, v_openDecls_1280_);
lean_ctor_set(v_reuseFailAlloc_1298_, 8, v_initHeartbeats_1281_);
lean_ctor_set(v_reuseFailAlloc_1298_, 9, v_maxHeartbeats_1282_);
lean_ctor_set(v_reuseFailAlloc_1298_, 10, v_quotContext_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 11, v_currMacroScope_1284_);
lean_ctor_set(v_reuseFailAlloc_1298_, 12, v_cancelTk_x3f_1285_);
lean_ctor_set(v_reuseFailAlloc_1298_, 13, v_inheritedTraceOptions_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*14 + 1, v_suppressElabErrors_1286_);
v___x_1295_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
uint8_t v___x_1296_; uint8_t v___x_1297_; 
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*14, v___x_1270_);
v___x_1296_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_1150_, v___x_1269_);
v___x_1297_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1291_);
lean_dec_ref(v_env_1291_);
if (v___x_1297_ == 0)
{
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1295_);
v___y_1166_ = v___x_1296_;
v___y_1167_ = v___x_1292_;
v_fileName_1168_ = v_fileName_1275_;
v_fileMap_1169_ = v_fileMap_1276_;
v_currRecDepth_1170_ = v_currRecDepth_1277_;
v_ref_1171_ = v_ref_1278_;
v_currNamespace_1172_ = v_currNamespace_1279_;
v_openDecls_1173_ = v_openDecls_1280_;
v_initHeartbeats_1174_ = v_initHeartbeats_1281_;
v_maxHeartbeats_1175_ = v_maxHeartbeats_1282_;
v_quotContext_1176_ = v_quotContext_1283_;
v_currMacroScope_1177_ = v_currMacroScope_1284_;
v_cancelTk_x3f_1178_ = v_cancelTk_x3f_1285_;
v_suppressElabErrors_1179_ = v_suppressElabErrors_1286_;
v_inheritedTraceOptions_1180_ = v_inheritedTraceOptions_1287_;
v___y_1181_ = v___y_1273_;
goto v___jp_1165_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1287_);
lean_dec(v_cancelTk_x3f_1285_);
lean_dec(v_currMacroScope_1284_);
lean_dec(v_quotContext_1283_);
lean_dec(v_maxHeartbeats_1282_);
lean_dec(v_initHeartbeats_1281_);
lean_dec(v_openDecls_1280_);
lean_dec(v_currNamespace_1279_);
lean_dec(v_ref_1278_);
lean_dec(v_currRecDepth_1277_);
lean_dec_ref(v_fileMap_1276_);
lean_dec_ref(v_fileName_1275_);
v___y_1232_ = v___x_1296_;
v___y_1233_ = v___x_1295_;
v___y_1234_ = v___y_1273_;
v___y_1235_ = v___x_1292_;
v___y_1236_ = v___x_1297_;
goto v___jp_1231_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1287_);
lean_dec(v_cancelTk_x3f_1285_);
lean_dec(v_currMacroScope_1284_);
lean_dec(v_quotContext_1283_);
lean_dec(v_maxHeartbeats_1282_);
lean_dec(v_initHeartbeats_1281_);
lean_dec(v_openDecls_1280_);
lean_dec(v_currNamespace_1279_);
lean_dec(v_ref_1278_);
lean_dec(v_currRecDepth_1277_);
lean_dec_ref(v_fileMap_1276_);
lean_dec_ref(v_fileName_1275_);
v___y_1232_ = v___x_1296_;
v___y_1233_ = v___x_1295_;
v___y_1234_ = v___y_1273_;
v___y_1235_ = v___x_1292_;
v___y_1236_ = v___x_1296_;
goto v___jp_1231_;
}
}
}
}
v___jp_1302_:
{
if (v___y_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v_env_1305_; lean_object* v_nextMacroScope_1306_; lean_object* v_ngen_1307_; lean_object* v_auxDeclNGen_1308_; lean_object* v_traceState_1309_; lean_object* v_messages_1310_; lean_object* v_infoState_1311_; lean_object* v_snapshotTasks_1312_; lean_object* v_newDecls_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1322_; 
v___x_1304_ = lean_st_ref_take(v___x_1164_);
v_env_1305_ = lean_ctor_get(v___x_1304_, 0);
v_nextMacroScope_1306_ = lean_ctor_get(v___x_1304_, 1);
v_ngen_1307_ = lean_ctor_get(v___x_1304_, 2);
v_auxDeclNGen_1308_ = lean_ctor_get(v___x_1304_, 3);
v_traceState_1309_ = lean_ctor_get(v___x_1304_, 4);
v_messages_1310_ = lean_ctor_get(v___x_1304_, 6);
v_infoState_1311_ = lean_ctor_get(v___x_1304_, 7);
v_snapshotTasks_1312_ = lean_ctor_get(v___x_1304_, 8);
v_newDecls_1313_ = lean_ctor_get(v___x_1304_, 9);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1304_, 5);
lean_dec(v_unused_1323_);
v___x_1315_ = v___x_1304_;
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_newDecls_1313_);
lean_inc(v_snapshotTasks_1312_);
lean_inc(v_infoState_1311_);
lean_inc(v_messages_1310_);
lean_inc(v_traceState_1309_);
lean_inc(v_auxDeclNGen_1308_);
lean_inc(v_ngen_1307_);
lean_inc(v_nextMacroScope_1306_);
lean_inc(v_env_1305_);
lean_dec(v___x_1304_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = l_Lean_Kernel_enableDiag(v_env_1305_, v___x_1270_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 5, v___x_1145_);
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1306_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1308_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1309_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_messages_1310_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1311_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_newDecls_1313_);
v___x_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_st_ref_set(v___x_1164_, v___x_1319_);
lean_inc(v___x_1164_);
v___y_1272_ = v___x_1267_;
v___y_1273_ = v___x_1164_;
goto v___jp_1271_;
}
}
}
else
{
lean_inc(v___x_1164_);
v___y_1272_ = v___x_1267_;
v___y_1273_ = v___x_1164_;
goto v___jp_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_1325_, lean_object* v_x_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1325_, v_x_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_1329_, lean_object* v_info_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1330_, v_x_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_info_1335_, lean_object* v_x_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_1334_, v_info_1335_, v_x_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_1339_, lean_object* v_x_1340_, lean_object* v___x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_st_mk_ref(v___x_1339_);
lean_inc(v___x_1345_);
v___x_1346_ = lean_apply_5(v_x_1340_, v___x_1341_, v___x_1345_, v___y_1342_, v___y_1343_, lean_box(0));
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1356_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_st_ref_get(v___x_1345_);
lean_dec(v___x_1345_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1347_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v___x_1345_);
v_a_1357_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1346_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1346_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_1365_, lean_object* v_x_1366_, lean_object* v___x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_1365_, v_x_1366_, v___x_1367_, v___y_1368_, v___y_1369_);
return v_res_1371_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1378_; uint64_t v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_1381_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set_uint64(v___x_1382_, sizeof(void*)*1, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
lean_ctor_set(v___x_1389_, 3, v___x_1388_);
lean_ctor_set(v___x_1389_, 4, v___x_1388_);
lean_ctor_set(v___x_1389_, 5, v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(32u);
v___x_1391_ = lean_mk_empty_array_with_capacity(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1393_ = ((size_t)5ULL);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_unsigned_to_nat(32u);
v___x_1396_ = lean_mk_empty_array_with_capacity(v___x_1395_);
v___x_1397_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_1398_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1396_);
lean_ctor_set(v___x_1398_, 2, v___x_1394_);
lean_ctor_set(v___x_1398_, 3, v___x_1394_);
lean_ctor_set_usize(v___x_1398_, 4, v___x_1393_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_ctor_set(v___x_1400_, 2, v___x_1399_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
lean_ctor_set(v___x_1400_, 4, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_1401_, lean_object* v_lctx_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_toCommandContextInfo_1413_; lean_object* v_mctx_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; 
v___x_1405_ = lean_box(1);
v___x_1406_ = 0;
v___x_1407_ = 1;
v___x_1408_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1412_, 0, v___x_1408_);
lean_ctor_set(v___x_1412_, 1, v___x_1405_);
lean_ctor_set(v___x_1412_, 2, v_lctx_1402_);
lean_ctor_set(v___x_1412_, 3, v___x_1410_);
lean_ctor_set(v___x_1412_, 4, v___x_1411_);
lean_ctor_set(v___x_1412_, 5, v___x_1409_);
lean_ctor_set(v___x_1412_, 6, v___x_1411_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*7, v___x_1406_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*7 + 1, v___x_1406_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*7 + 2, v___x_1406_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*7 + 3, v___x_1407_);
v_toCommandContextInfo_1413_ = lean_ctor_get(v_info_1401_, 0);
v_mctx_1414_ = lean_ctor_get(v_toCommandContextInfo_1413_, 3);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_1416_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_1414_);
v___x_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1418_, 0, v_mctx_1414_);
lean_ctor_set(v___x_1418_, 1, v___x_1415_);
lean_ctor_set(v___x_1418_, 2, v___x_1405_);
lean_ctor_set(v___x_1418_, 3, v___x_1416_);
lean_ctor_set(v___x_1418_, 4, v___x_1417_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1419_, 0, v___x_1418_);
lean_closure_set(v___f_1419_, 1, v_x_1403_);
lean_closure_set(v___f_1419_, 2, v___x_1412_);
v___x_1420_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1401_, v___f_1419_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_fst_1425_; lean_object* v___x_1427_; 
v_fst_1425_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_fst_1425_);
lean_dec(v_a_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_fst_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_fst_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1420_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1420_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_1438_, lean_object* v_lctx_1439_, lean_object* v_x_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1438_, v_lctx_1439_, v_x_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_1443_, lean_object* v_info_1444_, lean_object* v_lctx_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1444_, v_lctx_1445_, v_x_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_info_1450_, lean_object* v_lctx_1451_, lean_object* v_x_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_1449_, v_info_1450_, v_lctx_1451_, v_x_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_1455_, lean_object* v_lctx_1456_){
_start:
{
lean_object* v_toCommandContextInfo_1457_; lean_object* v_env_1458_; lean_object* v_mctx_1459_; lean_object* v_options_1460_; lean_object* v_currNamespace_1461_; lean_object* v_openDecls_1462_; lean_object* v___x_1463_; 
v_toCommandContextInfo_1457_ = lean_ctor_get(v_info_1455_, 0);
v_env_1458_ = lean_ctor_get(v_toCommandContextInfo_1457_, 0);
v_mctx_1459_ = lean_ctor_get(v_toCommandContextInfo_1457_, 3);
v_options_1460_ = lean_ctor_get(v_toCommandContextInfo_1457_, 4);
v_currNamespace_1461_ = lean_ctor_get(v_toCommandContextInfo_1457_, 5);
v_openDecls_1462_ = lean_ctor_get(v_toCommandContextInfo_1457_, 6);
lean_inc(v_openDecls_1462_);
lean_inc(v_currNamespace_1461_);
lean_inc_ref(v_options_1460_);
lean_inc_ref(v_mctx_1459_);
lean_inc_ref(v_env_1458_);
v___x_1463_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1463_, 0, v_env_1458_);
lean_ctor_set(v___x_1463_, 1, v_mctx_1459_);
lean_ctor_set(v___x_1463_, 2, v_lctx_1456_);
lean_ctor_set(v___x_1463_, 3, v_options_1460_);
lean_ctor_set(v___x_1463_, 4, v_currNamespace_1461_);
lean_ctor_set(v___x_1463_, 5, v_openDecls_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_1464_, lean_object* v_lctx_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1464_, v_lctx_1465_);
lean_dec_ref(v_info_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_1467_, lean_object* v_lctx_1468_, lean_object* v_stx_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1467_, v_lctx_1468_);
v___x_1472_ = l_Lean_ppTerm(v___x_1471_, v_stx_1469_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_1474_, lean_object* v_lctx_1475_, lean_object* v_stx_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_1474_, v_lctx_1475_, v_stx_1476_);
lean_dec_ref(v_info_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_1494_, lean_object* v_pos_1495_, lean_object* v_info_1496_){
_start:
{
lean_object* v_toCommandContextInfo_1497_; lean_object* v_fileMap_1498_; lean_object* v___x_1499_; lean_object* v_line_1500_; lean_object* v_column_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1524_; 
v_toCommandContextInfo_1497_ = lean_ctor_get(v_ctx_1494_, 0);
lean_inc_ref(v_toCommandContextInfo_1497_);
lean_dec_ref(v_ctx_1494_);
v_fileMap_1498_ = lean_ctor_get(v_toCommandContextInfo_1497_, 2);
lean_inc_ref(v_fileMap_1498_);
lean_dec_ref(v_toCommandContextInfo_1497_);
v___x_1499_ = l_Lean_FileMap_toPosition(v_fileMap_1498_, v_pos_1495_);
v_line_1500_ = lean_ctor_get(v___x_1499_, 0);
v_column_1501_ = lean_ctor_get(v___x_1499_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_column_1501_);
lean_inc(v_line_1500_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1506_ = l_Nat_reprFast(v_line_1500_);
v___x_1507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 5);
lean_ctor_set(v___x_1503_, 1, v___x_1507_);
lean_ctor_set(v___x_1503_, 0, v___x_1505_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_pos_1516_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_1511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Nat_reprFast(v_column_1501_);
v___x_1513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1511_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_1516_, 0, v___x_1514_);
lean_ctor_set(v_pos_1516_, 1, v___x_1515_);
switch(lean_obj_tag(v_info_1496_))
{
case 0:
{
return v_pos_1516_;
}
case 1:
{
uint8_t v_canonical_1520_; 
v_canonical_1520_ = lean_ctor_get_uint8(v_info_1496_, sizeof(void*)*2);
if (v_canonical_1520_ == 1)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_pos_1516_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
return v___x_1522_;
}
else
{
goto v___jp_1517_;
}
}
default: 
{
goto v___jp_1517_;
}
}
v___jp_1517_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_pos_1516_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_1525_, lean_object* v_pos_1526_, lean_object* v_info_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1525_, v_pos_1526_, v_info_1527_);
lean_dec(v_info_1527_);
lean_dec(v_pos_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_1532_, lean_object* v_stx_1533_){
_start:
{
lean_object* v___y_1535_; lean_object* v___y_1536_; uint8_t v___x_1544_; lean_object* v___y_1546_; lean_object* v___x_1549_; 
v___x_1544_ = 0;
v___x_1549_ = l_Lean_Syntax_getPos_x3f(v_stx_1533_, v___x_1544_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_unsigned_to_nat(0u);
v___y_1546_ = v___x_1550_;
goto v___jp_1545_;
}
else
{
lean_object* v_val_1551_; 
v_val_1551_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1551_);
lean_dec_ref(v___x_1549_);
v___y_1546_ = v_val_1551_;
goto v___jp_1545_;
}
v___jp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1537_ = l_Lean_Syntax_getHeadInfo(v_stx_1533_);
lean_inc_ref(v_ctx_1532_);
v___x_1538_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1532_, v___y_1535_, v___x_1537_);
lean_dec(v___x_1537_);
lean_dec(v___y_1535_);
v___x_1539_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_Syntax_getTailInfo(v_stx_1533_);
v___x_1542_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1532_, v___y_1536_, v___x_1541_);
lean_dec(v___x_1541_);
lean_dec(v___y_1536_);
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
return v___x_1543_;
}
v___jp_1545_:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1533_, v___x_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_inc(v___y_1546_);
v___y_1535_ = v___y_1546_;
v___y_1536_ = v___y_1546_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref(v___x_1547_);
v___y_1535_ = v___y_1546_;
v___y_1536_ = v_val_1548_;
goto v___jp_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_1552_, lean_object* v_stx_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1552_, v_stx_1553_);
lean_dec(v_stx_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_1558_, lean_object* v_info_1559_){
_start:
{
lean_object* v_elaborator_1560_; lean_object* v_stx_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1576_; 
v_elaborator_1560_ = lean_ctor_get(v_info_1559_, 0);
v_stx_1561_ = lean_ctor_get(v_info_1559_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_info_1559_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1563_ = v_info_1559_;
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_stx_1561_);
lean_inc(v_elaborator_1560_);
lean_dec(v_info_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_Name_isAnonymous(v_elaborator_1560_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1558_, v_stx_1561_);
lean_dec(v_stx_1561_);
v___x_1567_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 5);
lean_ctor_set(v___x_1563_, 1, v___x_1567_);
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1569_ = v___x_1563_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = 1;
v___x_1571_ = l_Lean_Name_toString(v_elaborator_1560_, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1569_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1575_; 
lean_del_object(v___x_1563_);
lean_dec(v_elaborator_1560_);
v___x_1575_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1558_, v_stx_1561_);
lean_dec(v_stx_1561_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_1577_, lean_object* v_ctx_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v_lctx_1581_; lean_object* v___x_1582_; 
v_lctx_1581_ = lean_ctor_get(v_info_1577_, 1);
lean_inc_ref(v_lctx_1581_);
lean_dec_ref(v_info_1577_);
v___x_1582_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1578_, v_lctx_1581_, v_x_1579_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_1583_, lean_object* v_ctx_1584_, lean_object* v_x_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1583_, v_ctx_1584_, v_x_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_1588_, lean_object* v_info_1589_, lean_object* v_ctx_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1589_, v_ctx_1590_, v_x_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_info_1595_, lean_object* v_ctx_1596_, lean_object* v_x_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_1594_, v_info_1595_, v_ctx_1596_, v_x_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_1614_, lean_object* v_toElabInfo_1615_, lean_object* v_expr_1616_, uint8_t v_isBinder_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v_a_1638_; lean_object* v___y_1648_; uint8_t v___y_1649_; lean_object* v___y_1652_; lean_object* v_a_1653_; lean_object* v___x_1656_; 
lean_inc(v___y_1621_);
lean_inc_ref(v___y_1620_);
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc_ref(v_expr_1616_);
v___x_1656_ = lean_infer_type(v_expr_1616_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___x_1658_ = l_Lean_Meta_ppExpr(v_a_1657_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v_a_1638_ = v_a_1659_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1660_; 
v_a_1660_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1660_);
v___y_1652_ = v___x_1658_;
v_a_1653_ = v_a_1660_;
goto v___jp_1651_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1656_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
lean_inc(v_a_1661_);
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
v___y_1652_ = v___x_1666_;
v_a_1653_ = v_a_1661_;
goto v___jp_1651_;
}
}
}
v___jp_1623_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v___y_1626_);
v___x_1627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1626_);
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___y_1624_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1614_, v_toElabInfo_1615_);
v___x_1635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_ppExpr(v_expr_1616_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1640_);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
if (v_isBinder_1617_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_1624_ = v_a_1638_;
v___y_1625_ = v___x_1644_;
v___y_1626_ = v___x_1645_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_1624_ = v_a_1638_;
v___y_1625_ = v___x_1644_;
v___y_1626_ = v___x_1646_;
goto v___jp_1623_;
}
}
else
{
lean_dec(v_a_1638_);
lean_dec_ref(v_toElabInfo_1615_);
lean_dec_ref(v_ctx_1614_);
return v___x_1639_;
}
}
v___jp_1647_:
{
if (v___y_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref(v___y_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_1638_ = v___x_1650_;
goto v___jp_1637_;
}
else
{
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v_expr_1616_);
lean_dec_ref(v_toElabInfo_1615_);
lean_dec_ref(v_ctx_1614_);
return v___y_1648_;
}
}
v___jp_1651_:
{
uint8_t v___x_1654_; 
v___x_1654_ = l_Lean_Exception_isInterrupt(v_a_1653_);
if (v___x_1654_ == 0)
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Lean_Exception_isRuntime(v_a_1653_);
v___y_1648_ = v___y_1652_;
v___y_1649_ = v___x_1655_;
goto v___jp_1647_;
}
else
{
lean_dec_ref(v_a_1653_);
v___y_1648_ = v___y_1652_;
v___y_1649_ = v___x_1654_;
goto v___jp_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_1669_, lean_object* v_toElabInfo_1670_, lean_object* v_expr_1671_, lean_object* v_isBinder_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_isBinder_boxed_1678_; lean_object* v_res_1679_; 
v_isBinder_boxed_1678_ = lean_unbox(v_isBinder_1672_);
v_res_1679_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_1669_, v_toElabInfo_1670_, v_expr_1671_, v_isBinder_boxed_1678_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_1680_, lean_object* v_info_1681_){
_start:
{
lean_object* v_toElabInfo_1683_; lean_object* v_expr_1684_; uint8_t v_isBinder_1685_; lean_object* v___x_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; 
v_toElabInfo_1683_ = lean_ctor_get(v_info_1681_, 0);
v_expr_1684_ = lean_ctor_get(v_info_1681_, 3);
v_isBinder_1685_ = lean_ctor_get_uint8(v_info_1681_, sizeof(void*)*4);
v___x_1686_ = lean_box(v_isBinder_1685_);
lean_inc_ref(v_expr_1684_);
lean_inc_ref(v_toElabInfo_1683_);
lean_inc_ref(v_ctx_1680_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1687_, 0, v_ctx_1680_);
lean_closure_set(v___f_1687_, 1, v_toElabInfo_1683_);
lean_closure_set(v___f_1687_, 2, v_expr_1684_);
lean_closure_set(v___f_1687_, 3, v___x_1686_);
v___x_1688_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1681_, v_ctx_1680_, v___f_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_1689_, lean_object* v_info_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Elab_TermInfo_format(v_ctx_1689_, v_info_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_1696_, lean_object* v_info_1697_){
_start:
{
lean_object* v_toElabInfo_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_toElabInfo_1698_ = lean_ctor_get(v_info_1697_, 0);
lean_inc_ref(v_toElabInfo_1698_);
lean_dec_ref(v_info_1697_);
v___x_1699_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_1700_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1696_, v_toElabInfo_1698_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_val_1710_ = lean_ctor_get(v_x_1708_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1708_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1712_ = v_x_1708_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_val_1710_);
lean_dec(v_x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1714_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1715_ = lean_expr_dbg_to_string(v_val_1710_);
lean_dec(v_val_1710_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 3);
lean_ctor_set(v___x_1712_, 0, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1714_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_1727_, lean_object* v_lctx_1728_, lean_object* v_stx_1729_, lean_object* v_expectedType_x3f_1730_, lean_object* v_info_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1756_; 
v___x_1737_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1727_, v_lctx_1728_, v_stx_1729_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1742_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1738_);
v___x_1744_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1730_);
v___x_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_Elab_CompletionInfo_stx(v_info_1731_);
v___x_1751_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1727_, v___x_1750_);
lean_dec(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1749_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1752_);
v___x_1754_ = v___x_1740_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_1757_, lean_object* v_lctx_1758_, lean_object* v_stx_1759_, lean_object* v_expectedType_x3f_1760_, lean_object* v_info_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_1757_, v_lctx_1758_, v_stx_1759_, v_expectedType_x3f_1760_, v_info_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_info_1761_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_1774_, lean_object* v_info_1775_){
_start:
{
switch(lean_obj_tag(v_info_1775_))
{
case 0:
{
lean_object* v_termInfo_1777_; lean_object* v_expectedType_x3f_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1799_; 
v_termInfo_1777_ = lean_ctor_get(v_info_1775_, 0);
v_expectedType_x3f_1778_ = lean_ctor_get(v_info_1775_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_info_1775_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1780_ = v_info_1775_;
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_expectedType_x3f_1778_);
lean_inc(v_termInfo_1777_);
lean_dec(v_info_1775_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Elab_TermInfo_format(v_ctx_1774_, v_termInfo_1777_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1798_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1798_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1798_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 5);
lean_ctor_set(v___x_1780_, 1, v_a_1783_);
lean_ctor_set(v___x_1780_, 0, v___x_1787_);
v___x_1789_ = v___x_1780_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_a_1783_);
v___x_1789_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1790_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1778_);
v___x_1793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1793_);
v___x_1795_ = v___x_1785_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_del_object(v___x_1780_);
lean_dec(v_expectedType_x3f_1778_);
return v___x_1782_;
}
}
}
case 1:
{
lean_object* v_stx_1800_; lean_object* v_lctx_1801_; lean_object* v_expectedType_x3f_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; 
v_stx_1800_ = lean_ctor_get(v_info_1775_, 0);
lean_inc(v_stx_1800_);
v_lctx_1801_ = lean_ctor_get(v_info_1775_, 2);
lean_inc_ref_n(v_lctx_1801_, 2);
v_expectedType_x3f_1802_ = lean_ctor_get(v_info_1775_, 3);
lean_inc(v_expectedType_x3f_1802_);
lean_inc_ref(v_ctx_1774_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1803_, 0, v_ctx_1774_);
lean_closure_set(v___f_1803_, 1, v_lctx_1801_);
lean_closure_set(v___f_1803_, 2, v_stx_1800_);
lean_closure_set(v___f_1803_, 3, v_expectedType_x3f_1802_);
lean_closure_set(v___f_1803_, 4, v_info_1775_);
v___x_1804_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1774_, v_lctx_1801_, v___f_1803_);
return v___x_1804_;
}
default: 
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1805_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_1806_ = l_Lean_Elab_CompletionInfo_stx(v_info_1775_);
lean_dec_ref(v_info_1775_);
v___x_1807_ = lean_box(0);
v___x_1808_ = 0;
lean_inc(v___x_1806_);
v___x_1809_ = l_Lean_Syntax_formatStx(v___x_1806_, v___x_1807_, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1805_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1774_, v___x_1806_);
lean_dec(v___x_1806_);
v___x_1814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_1816_, lean_object* v_info_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1816_, v_info_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_1823_, lean_object* v_info_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1826_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_1827_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1823_, v_info_1824_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_1830_, lean_object* v_info_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Elab_CommandInfo_format(v_ctx_1830_, v_info_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_1837_, lean_object* v_info_1838_){
_start:
{
lean_object* v_stx_1840_; lean_object* v_optionName_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_stx_1840_ = lean_ctor_get(v_info_1838_, 0);
lean_inc(v_stx_1840_);
v_optionName_1841_ = lean_ctor_get(v_info_1838_, 1);
lean_inc(v_optionName_1841_);
lean_dec_ref(v_info_1838_);
v___x_1842_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_1843_ = 1;
v___x_1844_ = l_Lean_Name_toString(v_optionName_1841_, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1842_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1837_, v_stx_1840_);
lean_dec(v_stx_1840_);
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_1852_, lean_object* v_info_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Elab_OptionInfo_format(v_ctx_1852_, v_info_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_1859_, lean_object* v_info_1860_){
_start:
{
lean_object* v_stx_1862_; lean_object* v_errorName_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1879_; 
v_stx_1862_ = lean_ctor_get(v_info_1860_, 0);
v_errorName_1863_ = lean_ctor_get(v_info_1860_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_info_1860_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1865_ = v_info_1860_;
v_isShared_1866_ = v_isSharedCheck_1879_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_errorName_1863_);
lean_inc(v_stx_1862_);
lean_dec(v_info_1860_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1879_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1867_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_1868_ = 1;
v___x_1869_ = l_Lean_Name_toString(v_errorName_1863_, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 5);
lean_ctor_set(v___x_1865_, 1, v___x_1870_);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1872_ = v___x_1865_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1859_, v_stx_1862_);
lean_dec(v_stx_1862_);
v___x_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_1880_, lean_object* v_info_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1880_, v_info_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1890_, lean_object* v_fieldName_1891_, lean_object* v_ctx_1892_, lean_object* v_stx_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc_ref(v_val_1890_);
v___x_1899_ = lean_infer_type(v_val_1890_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l_Lean_Meta_ppExpr(v_a_1900_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1932_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Meta_ppExpr(v_val_1890_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1931_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1931_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1931_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1911_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1912_ = 1;
v___x_1913_ = l_Lean_Name_toString(v_fieldName_1891_, v___x_1912_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 3);
lean_ctor_set(v___x_1904_, 0, v___x_1913_);
v___x_1915_ = v___x_1904_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_a_1902_);
v___x_1920_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_a_1907_);
v___x_1923_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1892_, v_stx_1893_);
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1926_);
v___x_1928_ = v___x_1909_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_del_object(v___x_1904_);
lean_dec(v_a_1902_);
lean_dec_ref(v_ctx_1892_);
lean_dec(v_fieldName_1891_);
return v___x_1906_;
}
}
}
else
{
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_ctx_1892_);
lean_dec(v_fieldName_1891_);
lean_dec_ref(v_val_1890_);
return v___x_1901_;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_ctx_1892_);
lean_dec(v_fieldName_1891_);
lean_dec_ref(v_val_1890_);
v_a_1933_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1899_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1899_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1941_, lean_object* v_fieldName_1942_, lean_object* v_ctx_1943_, lean_object* v_stx_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1941_, v_fieldName_1942_, v_ctx_1943_, v_stx_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v_stx_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1951_, lean_object* v_info_1952_){
_start:
{
lean_object* v_fieldName_1954_; lean_object* v_lctx_1955_; lean_object* v_val_1956_; lean_object* v_stx_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_fieldName_1954_ = lean_ctor_get(v_info_1952_, 1);
lean_inc(v_fieldName_1954_);
v_lctx_1955_ = lean_ctor_get(v_info_1952_, 2);
lean_inc_ref(v_lctx_1955_);
v_val_1956_ = lean_ctor_get(v_info_1952_, 3);
lean_inc_ref(v_val_1956_);
v_stx_1957_ = lean_ctor_get(v_info_1952_, 4);
lean_inc(v_stx_1957_);
lean_dec_ref(v_info_1952_);
lean_inc_ref(v_ctx_1951_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1958_, 0, v_val_1956_);
lean_closure_set(v___f_1958_, 1, v_fieldName_1954_);
lean_closure_set(v___f_1958_, 2, v_ctx_1951_);
lean_closure_set(v___f_1958_, 3, v_stx_1957_);
v___x_1959_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1951_, v_lctx_1955_, v___f_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1960_, lean_object* v_info_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Elab_FieldInfo_format(v_ctx_1960_, v_info_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_dec(v_pre_1964_);
return v_x_1965_;
}
else
{
lean_object* v_head_1967_; lean_object* v_tail_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1977_; 
v_head_1967_ = lean_ctor_get(v_x_1966_, 0);
v_tail_1968_ = lean_ctor_get(v_x_1966_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1966_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1970_ = v_x_1966_;
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_tail_1968_);
lean_inc(v_head_1967_);
lean_dec(v_x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
lean_inc(v_pre_1964_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 5);
lean_ctor_set(v___x_1970_, 1, v_pre_1964_);
lean_ctor_set(v___x_1970_, 0, v_x_1965_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_x_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_pre_1964_);
v___x_1973_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_head_1967_);
v_x_1965_ = v___x_1974_;
v_x_1966_ = v_tail_1968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1978_, lean_object* v_x_1979_){
_start:
{
if (lean_obj_tag(v_x_1979_) == 0)
{
lean_object* v___x_1980_; 
lean_dec(v_pre_1978_);
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
else
{
lean_object* v_head_1981_; lean_object* v_tail_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
v_head_1981_ = lean_ctor_get(v_x_1979_, 0);
v_tail_1982_ = lean_ctor_get(v_x_1979_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v_x_1979_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_tail_1982_);
lean_inc(v_head_1981_);
lean_dec(v_x_1979_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
lean_inc(v_pre_1978_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 5);
lean_ctor_set(v___x_1984_, 1, v_head_1981_);
lean_ctor_set(v___x_1984_, 0, v_pre_1978_);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_pre_1978_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_head_1981_);
v___x_1987_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1978_, v___x_1987_, v_tail_1982_);
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l_List_reverse___redArg(v_x_1992_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
else
{
lean_object* v_head_2000_; lean_object* v_tail_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2019_; 
v_head_2000_ = lean_ctor_get(v_x_1991_, 0);
v_tail_2001_ = lean_ctor_get(v_x_1991_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2003_ = v_x_1991_;
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_tail_2001_);
lean_inc(v_head_2000_);
lean_dec(v_x_1991_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Meta_ppGoal(v_head_2000_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v_head_2000_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_x_1992_);
lean_ctor_set(v___x_2003_, 0, v_a_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2006_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_x_1992_);
v___x_2008_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v_x_1991_ = v_tail_2001_;
v_x_1992_ = v___x_2008_;
goto _start;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_del_object(v___x_2003_);
lean_dec(v_tail_2001_);
lean_dec(v_x_1992_);
v_a_2011_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2005_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2005_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_2020_, v_x_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_2031_, lean_object* v___x_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_2031_, v___x_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2048_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2044_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2043_, v_a_2039_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v_a_2049_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2038_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2038_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_2057_, lean_object* v___x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_2057_, v___x_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(32u);
v___x_2069_ = lean_mk_empty_array_with_capacity(v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2071_ = ((size_t)5ULL);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_unsigned_to_nat(32u);
v___x_2074_ = lean_mk_empty_array_with_capacity(v___x_2073_);
v___x_2075_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2076_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
lean_ctor_set(v___x_2076_, 2, v___x_2072_);
lean_ctor_set(v___x_2076_, 3, v___x_2072_);
lean_ctor_set_usize(v___x_2076_, 4, v___x_2071_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_box(1);
v___x_2078_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2079_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_2080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
lean_ctor_set(v___x_2080_, 2, v___x_2077_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_2084_, lean_object* v_goals_2085_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = l_List_isEmpty___redArg(v_goals_2085_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; 
v___x_2088_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_2089_ = lean_box(0);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2090_, 0, v_goals_2085_);
lean_closure_set(v___f_2090_, 1, v___x_2089_);
v___x_2091_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_2084_, v___x_2088_, v___f_2090_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v_goals_2085_);
lean_dec_ref(v_ctx_2084_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_2094_, lean_object* v_goals_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_2094_, v_goals_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_2107_, lean_object* v_info_2108_){
_start:
{
lean_object* v_toCommandContextInfo_2110_; lean_object* v_parentDecl_x3f_2111_; lean_object* v_autoImplicits_2112_; lean_object* v_env_2113_; lean_object* v_cmdEnv_x3f_2114_; lean_object* v_fileMap_2115_; lean_object* v_options_2116_; lean_object* v_currNamespace_2117_; lean_object* v_openDecls_2118_; lean_object* v_ngen_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2161_; 
v_toCommandContextInfo_2110_ = lean_ctor_get(v_ctx_2107_, 0);
lean_inc_ref(v_toCommandContextInfo_2110_);
v_parentDecl_x3f_2111_ = lean_ctor_get(v_ctx_2107_, 1);
v_autoImplicits_2112_ = lean_ctor_get(v_ctx_2107_, 2);
v_env_2113_ = lean_ctor_get(v_toCommandContextInfo_2110_, 0);
v_cmdEnv_x3f_2114_ = lean_ctor_get(v_toCommandContextInfo_2110_, 1);
v_fileMap_2115_ = lean_ctor_get(v_toCommandContextInfo_2110_, 2);
v_options_2116_ = lean_ctor_get(v_toCommandContextInfo_2110_, 4);
v_currNamespace_2117_ = lean_ctor_get(v_toCommandContextInfo_2110_, 5);
v_openDecls_2118_ = lean_ctor_get(v_toCommandContextInfo_2110_, 6);
v_ngen_2119_ = lean_ctor_get(v_toCommandContextInfo_2110_, 7);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toCommandContextInfo_2110_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_toCommandContextInfo_2110_, 3);
lean_dec(v_unused_2162_);
v___x_2121_ = v_toCommandContextInfo_2110_;
v_isShared_2122_ = v_isSharedCheck_2161_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_ngen_2119_);
lean_inc(v_openDecls_2118_);
lean_inc(v_currNamespace_2117_);
lean_inc(v_options_2116_);
lean_inc(v_fileMap_2115_);
lean_inc(v_cmdEnv_x3f_2114_);
lean_inc(v_env_2113_);
lean_dec(v_toCommandContextInfo_2110_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2161_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_toElabInfo_2123_; lean_object* v_mctxBefore_2124_; lean_object* v_goalsBefore_2125_; lean_object* v_mctxAfter_2126_; lean_object* v_goalsAfter_2127_; lean_object* v___x_2129_; 
v_toElabInfo_2123_ = lean_ctor_get(v_info_2108_, 0);
lean_inc_ref(v_toElabInfo_2123_);
v_mctxBefore_2124_ = lean_ctor_get(v_info_2108_, 1);
lean_inc_ref(v_mctxBefore_2124_);
v_goalsBefore_2125_ = lean_ctor_get(v_info_2108_, 2);
lean_inc(v_goalsBefore_2125_);
v_mctxAfter_2126_ = lean_ctor_get(v_info_2108_, 3);
lean_inc_ref(v_mctxAfter_2126_);
v_goalsAfter_2127_ = lean_ctor_get(v_info_2108_, 4);
lean_inc(v_goalsAfter_2127_);
lean_dec_ref(v_info_2108_);
lean_inc_ref(v_ngen_2119_);
lean_inc(v_openDecls_2118_);
lean_inc(v_currNamespace_2117_);
lean_inc_ref(v_options_2116_);
lean_inc_ref(v_fileMap_2115_);
lean_inc(v_cmdEnv_x3f_2114_);
lean_inc_ref(v_env_2113_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 3, v_mctxBefore_2124_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_env_2113_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_cmdEnv_x3f_2114_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_fileMap_2115_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_mctxBefore_2124_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_options_2116_);
lean_ctor_set(v_reuseFailAlloc_2160_, 5, v_currNamespace_2117_);
lean_ctor_set(v_reuseFailAlloc_2160_, 6, v_openDecls_2118_);
lean_ctor_set(v_reuseFailAlloc_2160_, 7, v_ngen_2119_);
v___x_2129_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v_ctxB_2130_; lean_object* v___x_2131_; 
lean_inc_ref(v_autoImplicits_2112_);
lean_inc(v_parentDecl_x3f_2111_);
v_ctxB_2130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_2130_, 0, v___x_2129_);
lean_ctor_set(v_ctxB_2130_, 1, v_parentDecl_x3f_2111_);
lean_ctor_set(v_ctxB_2130_, 2, v_autoImplicits_2112_);
v___x_2131_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_2130_, v_goalsBefore_2125_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v_ctxA_2134_; lean_object* v___x_2135_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2133_, 0, v_env_2113_);
lean_ctor_set(v___x_2133_, 1, v_cmdEnv_x3f_2114_);
lean_ctor_set(v___x_2133_, 2, v_fileMap_2115_);
lean_ctor_set(v___x_2133_, 3, v_mctxAfter_2126_);
lean_ctor_set(v___x_2133_, 4, v_options_2116_);
lean_ctor_set(v___x_2133_, 5, v_currNamespace_2117_);
lean_ctor_set(v___x_2133_, 6, v_openDecls_2118_);
lean_ctor_set(v___x_2133_, 7, v_ngen_2119_);
lean_inc_ref(v_autoImplicits_2112_);
lean_inc(v_parentDecl_x3f_2111_);
v_ctxA_2134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_2134_, 0, v___x_2133_);
lean_ctor_set(v_ctxA_2134_, 1, v_parentDecl_x3f_2111_);
lean_ctor_set(v_ctxA_2134_, 2, v_autoImplicits_2112_);
v___x_2135_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_2134_, v_goalsAfter_2127_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2159_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2159_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2159_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_stx_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v_stx_2140_ = lean_ctor_get(v_toElabInfo_2123_, 1);
lean_inc(v_stx_2140_);
v___x_2141_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_2142_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2107_, v_toElabInfo_2123_);
v___x_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_box(0);
v___x_2147_ = 0;
v___x_2148_ = l_Lean_Syntax_formatStx(v_stx_2140_, v___x_2146_, v___x_2147_);
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2145_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_a_2132_);
v___x_2153_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2155_);
v___x_2157_ = v___x_2138_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_dec(v_a_2132_);
lean_dec_ref(v_toElabInfo_2123_);
lean_dec_ref(v_ctx_2107_);
return v___x_2135_;
}
}
else
{
lean_dec(v_goalsAfter_2127_);
lean_dec_ref(v_mctxAfter_2126_);
lean_dec_ref(v_toElabInfo_2123_);
lean_dec_ref(v_ngen_2119_);
lean_dec(v_openDecls_2118_);
lean_dec(v_currNamespace_2117_);
lean_dec_ref(v_options_2116_);
lean_dec_ref(v_fileMap_2115_);
lean_dec(v_cmdEnv_x3f_2114_);
lean_dec_ref(v_env_2113_);
lean_dec_ref(v_ctx_2107_);
return v___x_2131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_2163_, lean_object* v_info_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Elab_TacticInfo_format(v_ctx_2163_, v_info_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_2173_, lean_object* v_info_2174_){
_start:
{
lean_object* v_lctx_2176_; lean_object* v_stx_2177_; lean_object* v_output_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2194_; 
v_lctx_2176_ = lean_ctor_get(v_info_2174_, 0);
lean_inc_ref_n(v_lctx_2176_, 2);
v_stx_2177_ = lean_ctor_get(v_info_2174_, 1);
lean_inc(v_stx_2177_);
v_output_2178_ = lean_ctor_get(v_info_2174_, 2);
lean_inc(v_output_2178_);
lean_dec_ref(v_info_2174_);
v___x_2179_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2173_, v_lctx_2176_, v_stx_2177_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
v___x_2181_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2173_, v_lctx_2176_, v_output_2178_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2186_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v_a_2180_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_a_2182_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2190_);
v___x_2192_ = v___x_2184_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_2195_, lean_object* v_info_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2195_, v_info_2196_);
lean_dec_ref(v_ctx_2195_);
return v_res_2198_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = 1;
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_2205_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
lean_ctor_set_usize(v___x_2205_, 2, v___x_2203_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*3, v___x_2202_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_2209_){
_start:
{
lean_object* v_toWidgetInstance_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2239_; 
v_toWidgetInstance_2210_ = lean_ctor_get(v_info_2209_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_info_2209_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v_info_2209_, 1);
lean_dec(v_unused_2240_);
v___x_2212_ = v_info_2209_;
v_isShared_2213_ = v_isSharedCheck_2239_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_toWidgetInstance_2210_);
lean_dec(v_info_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2239_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_id_2214_; lean_object* v_props_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v_fst_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2237_; 
v_id_2214_ = lean_ctor_get(v_toWidgetInstance_2210_, 0);
lean_inc(v_id_2214_);
v_props_2215_ = lean_ctor_get(v_toWidgetInstance_2210_, 1);
lean_inc_ref(v_props_2215_);
lean_dec_ref(v_toWidgetInstance_2210_);
v___x_2216_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_2217_ = lean_apply_1(v_props_2215_, v___x_2216_);
v_fst_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v___x_2217_, 1);
lean_dec(v_unused_2238_);
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2237_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_fst_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2237_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2222_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_2223_ = 1;
v___x_2224_ = l_Lean_Name_toString(v_id_2214_, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set_tag(v___x_2220_, 5);
lean_ctor_set(v___x_2220_, 1, v___x_2225_);
lean_ctor_set(v___x_2220_, 0, v___x_2222_);
v___x_2227_ = v___x_2220_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 5);
lean_ctor_set(v___x_2212_, 1, v___x_2228_);
lean_ctor_set(v___x_2212_, 0, v___x_2227_);
v___x_2230_ = v___x_2212_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2231_ = lean_unsigned_to_nat(80u);
v___x_2232_ = l_Lean_Json_pretty(v_fst_2218_, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2230_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
return v___x_2234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_2247_){
_start:
{
lean_object* v_userName_2248_; lean_object* v_id_2249_; lean_object* v_baseId_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_userName_2248_ = lean_ctor_get(v_info_2247_, 0);
lean_inc(v_userName_2248_);
v_id_2249_ = lean_ctor_get(v_info_2247_, 1);
lean_inc(v_id_2249_);
v_baseId_2250_ = lean_ctor_get(v_info_2247_, 2);
lean_inc(v_baseId_2250_);
lean_dec_ref(v_info_2247_);
v___x_2251_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_2252_ = lean_erase_macro_scopes(v_userName_2248_);
v___x_2253_ = 1;
v___x_2254_ = l_Lean_Name_toString(v___x_2252_, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2251_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_2258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_Name_toString(v_id_2249_, v___x_2253_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_2263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_Name_toString(v_baseId_2250_, v___x_2253_);
v___x_2265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2263_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_2270_, lean_object* v_info_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_2273_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_2270_, v_info_2271_);
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_2275_, lean_object* v_info_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2275_, v_info_2276_);
lean_dec(v_info_2276_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_2280_, lean_object* v_info_2281_){
_start:
{
lean_object* v_mkDocString_x3f_2283_; 
v_mkDocString_x3f_2283_ = lean_ctor_get(v_info_2281_, 2);
lean_inc(v_mkDocString_x3f_2283_);
lean_dec_ref(v_info_2281_);
if (lean_obj_tag(v_mkDocString_x3f_2283_) == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_ppCtx_2280_);
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2318_; 
v_val_2286_ = lean_ctor_get(v_mkDocString_x3f_2283_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_mkDocString_x3f_2283_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2288_ = v_mkDocString_x3f_2283_;
v_isShared_2289_ = v_isSharedCheck_2318_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v_mkDocString_x3f_2283_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2318_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_apply_2(v_val_2286_, v_ppCtx_2280_, lean_box(0));
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2301_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_a_2291_);
v___x_2296_ = v___x_2288_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2298_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2296_);
v___x_2298_ = v___x_2293_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2317_; 
v_a_2302_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2304_ = v___x_2290_;
v_isShared_2305_ = v_isSharedCheck_2317_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2290_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2317_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2306_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_2307_ = lean_io_error_to_string(v_a_2302_);
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2310_);
v___x_2312_ = v___x_2288_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2312_);
v___x_2314_ = v___x_2304_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_2319_, lean_object* v_info_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_2319_, v_info_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
if (lean_obj_tag(v_x_2323_) == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2325_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2337_; 
v_val_2326_ = lean_ctor_get(v_x_2323_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2323_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2328_ = v_x_2323_;
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v_x_2323_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2331_ = l_String_quote(v_val_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 3);
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2330_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Repr_addAppParen(v___x_2334_, v_x_2324_);
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2338_, v_x_2339_);
lean_dec(v_x_2339_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2355_, lean_object* v_info_2356_){
_start:
{
lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v_toTermInfo_2364_; lean_object* v_location_x3f_2365_; uint8_t v_explicit_2366_; lean_object* v___y_2368_; 
v_toTermInfo_2364_ = lean_ctor_get(v_info_2356_, 0);
lean_inc_ref(v_toTermInfo_2364_);
v_location_x3f_2365_ = lean_ctor_get(v_info_2356_, 1);
lean_inc(v_location_x3f_2365_);
v_explicit_2366_ = lean_ctor_get_uint8(v_info_2356_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_2365_) == 1)
{
lean_object* v_val_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2450_; 
v_val_2389_ = lean_ctor_get(v_location_x3f_2365_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_location_x3f_2365_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2391_ = v_location_x3f_2365_;
v_isShared_2392_ = v_isSharedCheck_2450_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_val_2389_);
lean_dec(v_location_x3f_2365_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2450_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_range_2393_; lean_object* v_pos_2394_; lean_object* v_endPos_2395_; lean_object* v_module_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2448_; 
v_range_2393_ = lean_ctor_get(v_val_2389_, 1);
v_pos_2394_ = lean_ctor_get(v_range_2393_, 0);
lean_inc_ref(v_pos_2394_);
v_endPos_2395_ = lean_ctor_get(v_range_2393_, 2);
lean_inc_ref(v_endPos_2395_);
v_module_2396_ = lean_ctor_get(v_val_2389_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_val_2389_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v_val_2389_, 1);
lean_dec(v_unused_2449_);
v___x_2398_ = v_val_2389_;
v_isShared_2399_ = v_isSharedCheck_2448_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_module_2396_);
lean_dec(v_val_2389_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2448_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_line_2400_; lean_object* v_column_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2447_; 
v_line_2400_ = lean_ctor_get(v_pos_2394_, 0);
v_column_2401_ = lean_ctor_get(v_pos_2394_, 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_pos_2394_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2403_ = v_pos_2394_;
v_isShared_2404_ = v_isSharedCheck_2447_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_column_2401_);
lean_inc(v_line_2400_);
lean_dec(v_pos_2394_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2447_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_line_2405_; lean_object* v_column_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2446_; 
v_line_2405_ = lean_ctor_get(v_endPos_2395_, 0);
v_column_2406_ = lean_ctor_get(v_endPos_2395_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_endPos_2395_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2408_ = v_endPos_2395_;
v_isShared_2409_ = v_isSharedCheck_2446_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_column_2406_);
lean_inc(v_line_2405_);
lean_dec(v_endPos_2395_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2446_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2410_ = 1;
v___x_2411_ = l_Lean_Name_toString(v_module_2396_, v___x_2410_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 3);
lean_ctor_set(v___x_2391_, 0, v___x_2411_);
v___x_2413_ = v___x_2391_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 5);
lean_ctor_set(v___x_2408_, 1, v___x_2414_);
lean_ctor_set(v___x_2408_, 0, v___x_2413_);
v___x_2416_ = v___x_2408_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2418_ = l_Nat_reprFast(v_line_2400_);
v___x_2419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 5);
lean_ctor_set(v___x_2403_, 1, v___x_2419_);
lean_ctor_set(v___x_2403_, 0, v___x_2417_);
v___x_2421_ = v___x_2403_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2399_ == 0)
{
lean_ctor_set_tag(v___x_2398_, 5);
lean_ctor_set(v___x_2398_, 1, v___x_2422_);
lean_ctor_set(v___x_2398_, 0, v___x_2421_);
v___x_2424_ = v___x_2398_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2425_ = l_Nat_reprFast(v_column_2401_);
v___x_2426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2424_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2416_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = l_Nat_reprFast(v_line_2405_);
v___x_2434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2417_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2422_);
v___x_2437_ = l_Nat_reprFast(v_column_2406_);
v___x_2438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2436_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___x_2428_);
v___x_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2432_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___y_2368_ = v___x_2441_;
goto v___jp_2367_;
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
lean_object* v___x_2451_; 
lean_dec(v_location_x3f_2365_);
v___x_2451_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2368_ = v___x_2451_;
goto v___jp_2367_;
}
v___jp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_inc_ref(v___y_2360_);
v___x_2361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___y_2360_);
v___x_2362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___y_2359_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
v___jp_2367_:
{
lean_object* v_lctx_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_lctx_2369_ = lean_ctor_get(v_toTermInfo_2364_, 1);
lean_inc_ref(v_lctx_2369_);
v___x_2370_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_2355_, v_lctx_2369_);
v___x_2371_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_2370_, v_info_2356_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = l_Lean_Elab_TermInfo_format(v_ctx_2355_, v_toTermInfo_2364_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v_a_2374_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___y_2368_);
v___x_2380_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_2372_, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
if (v_explicit_2366_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2359_ = v___x_2386_;
v___y_2360_ = v___x_2387_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2359_ = v___x_2386_;
v___y_2360_ = v___x_2388_;
goto v___jp_2358_;
}
}
else
{
lean_dec(v_a_2372_);
lean_dec(v___y_2368_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2452_, lean_object* v_info_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2452_, v_info_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2459_, lean_object* v_info_2460_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2462_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2459_, v_info_2460_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2467_, lean_object* v_info_2468_){
_start:
{
lean_object* v_stx_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_stx_2469_ = lean_ctor_get(v_info_2468_, 1);
v___x_2470_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2469_);
v___x_2471_ = l_Lean_Syntax_getKind(v_stx_2469_);
v___x_2472_ = 1;
v___x_2473_ = l_Lean_Name_toString(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2470_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2467_, v_info_2468_);
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2489_, lean_object* v_info_2490_){
_start:
{
lean_object* v_toElabInfo_2491_; lean_object* v_name_2492_; uint8_t v_kind_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_toElabInfo_2491_ = lean_ctor_get(v_info_2490_, 0);
lean_inc_ref(v_toElabInfo_2491_);
v_name_2492_ = lean_ctor_get(v_info_2490_, 1);
lean_inc(v_name_2492_);
v_kind_2493_ = lean_ctor_get_uint8(v_info_2490_, sizeof(void*)*2);
lean_dec_ref(v_info_2490_);
v___x_2494_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2495_ = 1;
v___x_2496_ = l_Lean_Name_toString(v_name_2492_, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2494_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2493_, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2500_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2489_, v_toElabInfo_2491_);
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2508_, lean_object* v_x_2509_){
_start:
{
switch(lean_obj_tag(v_x_2509_))
{
case 0:
{
lean_object* v_i_2511_; lean_object* v___x_2512_; 
v_i_2511_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2511_);
lean_dec_ref(v_x_2509_);
v___x_2512_ = l_Lean_Elab_TacticInfo_format(v_ctx_2508_, v_i_2511_);
return v___x_2512_;
}
case 1:
{
lean_object* v_i_2513_; lean_object* v___x_2514_; 
v_i_2513_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2513_);
lean_dec_ref(v_x_2509_);
v___x_2514_ = l_Lean_Elab_TermInfo_format(v_ctx_2508_, v_i_2513_);
return v___x_2514_;
}
case 2:
{
lean_object* v_i_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2523_; 
v_i_2515_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2517_ = v_x_2509_;
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_i_2515_);
lean_dec(v_x_2509_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2508_, v_i_2515_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set_tag(v___x_2517_, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
case 3:
{
lean_object* v_i_2524_; lean_object* v___x_2525_; 
v_i_2524_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2524_);
lean_dec_ref(v_x_2509_);
v___x_2525_ = l_Lean_Elab_CommandInfo_format(v_ctx_2508_, v_i_2524_);
return v___x_2525_;
}
case 4:
{
lean_object* v_i_2526_; lean_object* v___x_2527_; 
v_i_2526_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2526_);
lean_dec_ref(v_x_2509_);
v___x_2527_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2508_, v_i_2526_);
lean_dec_ref(v_ctx_2508_);
return v___x_2527_;
}
case 5:
{
lean_object* v_i_2528_; lean_object* v___x_2529_; 
v_i_2528_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2528_);
lean_dec_ref(v_x_2509_);
v___x_2529_ = l_Lean_Elab_OptionInfo_format(v_ctx_2508_, v_i_2528_);
return v___x_2529_;
}
case 6:
{
lean_object* v_i_2530_; lean_object* v___x_2531_; 
v_i_2530_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2530_);
lean_dec_ref(v_x_2509_);
v___x_2531_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2508_, v_i_2530_);
return v___x_2531_;
}
case 7:
{
lean_object* v_i_2532_; lean_object* v___x_2533_; 
v_i_2532_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2532_);
lean_dec_ref(v_x_2509_);
v___x_2533_ = l_Lean_Elab_FieldInfo_format(v_ctx_2508_, v_i_2532_);
return v___x_2533_;
}
case 8:
{
lean_object* v_i_2534_; lean_object* v___x_2535_; 
v_i_2534_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2534_);
lean_dec_ref(v_x_2509_);
v___x_2535_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2508_, v_i_2534_);
return v___x_2535_;
}
case 9:
{
lean_object* v_i_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v_ctx_2508_);
v_i_2536_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v_x_2509_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_i_2536_);
lean_dec(v_x_2509_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
case 10:
{
lean_object* v_i_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_ctx_2508_);
v_i_2545_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2547_ = v_x_2509_;
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_i_2545_);
lean_dec(v_x_2509_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = l_Lean_Elab_CustomInfo_format(v_i_2545_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2549_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
case 11:
{
lean_object* v_i_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_ctx_2508_);
v_i_2554_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2556_ = v_x_2509_;
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_i_2554_);
lean_dec(v_x_2509_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2554_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set_tag(v___x_2556_, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2558_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
case 12:
{
lean_object* v_i_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
v_i_2563_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v_x_2509_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_i_2563_);
lean_dec(v_x_2509_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2508_, v_i_2563_);
lean_dec(v_i_2563_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
case 13:
{
lean_object* v_i_2572_; lean_object* v___x_2573_; 
v_i_2572_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_i_2572_);
lean_dec_ref(v_x_2509_);
v___x_2573_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2508_, v_i_2572_);
return v___x_2573_;
}
case 14:
{
lean_object* v_i_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2582_; 
v_i_2574_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2576_ = v_x_2509_;
v_isShared_2577_ = v_isSharedCheck_2582_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_i_2574_);
lean_dec(v_x_2509_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2582_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2508_, v_i_2574_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
case 15:
{
lean_object* v_i_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2591_; 
v_i_2583_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2585_ = v_x_2509_;
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_i_2583_);
lean_dec(v_x_2509_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = l_Lean_Elab_DocInfo_format(v_ctx_2508_, v_i_2583_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
default: 
{
lean_object* v_i_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_i_2592_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2594_ = v_x_2509_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_i_2592_);
lean_dec(v_x_2509_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2508_, v_i_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set_tag(v___x_2594_, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2601_, lean_object* v_x_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Elab_Info_format(v_ctx_2601_, v_x_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2605_){
_start:
{
switch(lean_obj_tag(v_x_2605_))
{
case 0:
{
lean_object* v_i_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_i_2606_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v_x_2605_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_i_2606_);
lean_dec(v_x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_toElabInfo_2610_; lean_object* v___x_2612_; 
v_toElabInfo_2610_ = lean_ctor_get(v_i_2606_, 0);
lean_inc_ref(v_toElabInfo_2610_);
lean_dec_ref(v_i_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set_tag(v___x_2608_, 1);
lean_ctor_set(v___x_2608_, 0, v_toElabInfo_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_toElabInfo_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
case 1:
{
lean_object* v_i_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_i_2615_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v_x_2605_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_i_2615_);
lean_dec(v_x_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_toElabInfo_2619_; lean_object* v___x_2621_; 
v_toElabInfo_2619_ = lean_ctor_get(v_i_2615_, 0);
lean_inc_ref(v_toElabInfo_2619_);
lean_dec_ref(v_i_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_toElabInfo_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_toElabInfo_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
case 2:
{
lean_object* v_i_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
v_i_2624_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2626_ = v_x_2605_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_i_2624_);
lean_dec(v_x_2605_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_toElabInfo_2628_; lean_object* v___x_2630_; 
v_toElabInfo_2628_ = lean_ctor_get(v_i_2624_, 0);
lean_inc_ref(v_toElabInfo_2628_);
lean_dec_ref(v_i_2624_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 1);
lean_ctor_set(v___x_2626_, 0, v_toElabInfo_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_toElabInfo_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
case 3:
{
lean_object* v_i_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_i_2633_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v_x_2605_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_i_2633_);
lean_dec(v_x_2605_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_i_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
case 13:
{
lean_object* v_i_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2650_; 
v_i_2641_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2643_ = v_x_2605_;
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_i_2641_);
lean_dec(v_x_2605_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_toTermInfo_2645_; lean_object* v_toElabInfo_2646_; lean_object* v___x_2648_; 
v_toTermInfo_2645_ = lean_ctor_get(v_i_2641_, 0);
lean_inc_ref(v_toTermInfo_2645_);
lean_dec_ref(v_i_2641_);
v_toElabInfo_2646_ = lean_ctor_get(v_toTermInfo_2645_, 0);
lean_inc_ref(v_toElabInfo_2646_);
lean_dec_ref(v_toTermInfo_2645_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
lean_ctor_set(v___x_2643_, 0, v_toElabInfo_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_toElabInfo_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
case 14:
{
lean_object* v_i_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_i_2651_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v_x_2605_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_i_2651_);
lean_dec(v_x_2605_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_i_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
case 15:
{
lean_object* v_i_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_i_2659_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v_x_2605_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_i_2659_);
lean_dec(v_x_2605_);
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
case 16:
{
lean_object* v_i_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2675_; 
v_i_2667_ = lean_ctor_get(v_x_2605_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_x_2605_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2669_ = v_x_2605_;
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_i_2667_);
lean_dec(v_x_2605_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_toElabInfo_2671_; lean_object* v___x_2673_; 
v_toElabInfo_2671_ = lean_ctor_get(v_i_2667_, 0);
lean_inc_ref(v_toElabInfo_2671_);
lean_dec_ref(v_i_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 0, v_toElabInfo_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_toElabInfo_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
default: 
{
lean_object* v___x_2676_; 
lean_dec_ref(v_x_2605_);
v___x_2676_ = lean_box(0);
return v___x_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2677_, lean_object* v_x_2678_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 1)
{
if (lean_obj_tag(v_x_2678_) == 0)
{
lean_object* v_val_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2714_; 
v_val_2679_ = lean_ctor_get(v_x_2677_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_x_2677_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2681_ = v_x_2677_;
v_isShared_2682_ = v_isSharedCheck_2714_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_val_2679_);
lean_dec(v_x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2714_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_toCommandContextInfo_2683_; lean_object* v_i_2684_; lean_object* v_parentDecl_x3f_2685_; lean_object* v_autoImplicits_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2712_; 
v_toCommandContextInfo_2683_ = lean_ctor_get(v_val_2679_, 0);
lean_inc_ref(v_toCommandContextInfo_2683_);
v_i_2684_ = lean_ctor_get(v_x_2678_, 0);
v_parentDecl_x3f_2685_ = lean_ctor_get(v_val_2679_, 1);
v_autoImplicits_2686_ = lean_ctor_get(v_val_2679_, 2);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_val_2679_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v_val_2679_, 0);
lean_dec(v_unused_2713_);
v___x_2688_ = v_val_2679_;
v_isShared_2689_ = v_isSharedCheck_2712_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_autoImplicits_2686_);
lean_inc(v_parentDecl_x3f_2685_);
lean_dec(v_val_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2712_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_env_2690_; lean_object* v_cmdEnv_x3f_2691_; lean_object* v_fileMap_2692_; lean_object* v_options_2693_; lean_object* v_currNamespace_2694_; lean_object* v_openDecls_2695_; lean_object* v_ngen_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2710_; 
v_env_2690_ = lean_ctor_get(v_toCommandContextInfo_2683_, 0);
v_cmdEnv_x3f_2691_ = lean_ctor_get(v_toCommandContextInfo_2683_, 1);
v_fileMap_2692_ = lean_ctor_get(v_toCommandContextInfo_2683_, 2);
v_options_2693_ = lean_ctor_get(v_toCommandContextInfo_2683_, 4);
v_currNamespace_2694_ = lean_ctor_get(v_toCommandContextInfo_2683_, 5);
v_openDecls_2695_ = lean_ctor_get(v_toCommandContextInfo_2683_, 6);
v_ngen_2696_ = lean_ctor_get(v_toCommandContextInfo_2683_, 7);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_toCommandContextInfo_2683_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v_toCommandContextInfo_2683_, 3);
lean_dec(v_unused_2711_);
v___x_2698_ = v_toCommandContextInfo_2683_;
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_ngen_2696_);
lean_inc(v_openDecls_2695_);
lean_inc(v_currNamespace_2694_);
lean_inc(v_options_2693_);
lean_inc(v_fileMap_2692_);
lean_inc(v_cmdEnv_x3f_2691_);
lean_inc(v_env_2690_);
lean_dec(v_toCommandContextInfo_2683_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_mctxAfter_2700_; lean_object* v___x_2702_; 
v_mctxAfter_2700_ = lean_ctor_get(v_i_2684_, 3);
lean_inc_ref(v_mctxAfter_2700_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 3, v_mctxAfter_2700_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_env_2690_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_cmdEnv_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_fileMap_2692_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_mctxAfter_2700_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_options_2693_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v_currNamespace_2694_);
lean_ctor_set(v_reuseFailAlloc_2709_, 6, v_openDecls_2695_);
lean_ctor_set(v_reuseFailAlloc_2709_, 7, v_ngen_2696_);
v___x_2702_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2702_);
v___x_2704_ = v___x_2688_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_parentDecl_x3f_2685_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_autoImplicits_2686_);
v___x_2704_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2704_);
v___x_2706_ = v___x_2681_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
}
else
{
return v_x_2677_;
}
}
else
{
return v_x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2715_, lean_object* v_x_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2715_, v_x_2716_);
lean_dec_ref(v_x_2716_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 0)
{
return v_x_2718_;
}
else
{
lean_object* v_head_2720_; lean_object* v_tail_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_head_2720_ = lean_ctor_get(v_x_2719_, 0);
v_tail_2721_ = lean_ctor_get(v_x_2719_, 1);
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2723_ = lean_string_append(v_x_2718_, v___x_2722_);
v___x_2724_ = lean_expr_dbg_to_string(v_head_2720_);
v___x_2725_ = lean_string_append(v___x_2723_, v___x_2724_);
lean_dec_ref(v___x_2724_);
v_x_2718_ = v___x_2725_;
v_x_2719_ = v_tail_2721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2727_, lean_object* v_x_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2727_, v_x_2728_);
lean_dec(v_x_2728_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2732_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2733_;
}
else
{
lean_object* v_tail_2734_; 
v_tail_2734_ = lean_ctor_get(v_x_2732_, 1);
if (lean_obj_tag(v_tail_2734_) == 0)
{
lean_object* v_head_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_head_2735_ = lean_ctor_get(v_x_2732_, 0);
v___x_2736_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2737_ = lean_expr_dbg_to_string(v_head_2735_);
v___x_2738_ = lean_string_append(v___x_2736_, v___x_2737_);
lean_dec_ref(v___x_2737_);
v___x_2739_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2740_ = lean_string_append(v___x_2738_, v___x_2739_);
return v___x_2740_;
}
else
{
lean_object* v_head_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint32_t v___x_2746_; lean_object* v___x_2747_; 
v_head_2741_ = lean_ctor_get(v_x_2732_, 0);
v___x_2742_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2743_ = lean_expr_dbg_to_string(v_head_2741_);
v___x_2744_ = lean_string_append(v___x_2742_, v___x_2743_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2744_, v_tail_2734_);
v___x_2746_ = 93;
v___x_2747_ = lean_string_push(v___x_2745_, v___x_2746_);
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2748_);
lean_dec(v_x_2748_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2756_){
_start:
{
switch(lean_obj_tag(v_ctx_2756_))
{
case 0:
{
lean_object* v___x_2757_; 
lean_dec_ref(v_ctx_2756_);
v___x_2757_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2757_;
}
case 1:
{
lean_object* v_parentDecl_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2771_; 
v_parentDecl_2758_ = lean_ctor_get(v_ctx_2756_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_ctx_2756_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2760_ = v_ctx_2756_;
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_parentDecl_2758_);
lean_dec(v_ctx_2756_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2762_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2763_ = 1;
v___x_2764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2758_, v___x_2763_);
v___x_2765_ = lean_string_append(v___x_2762_, v___x_2764_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2767_ = lean_string_append(v___x_2765_, v___x_2766_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 3);
lean_ctor_set(v___x_2760_, 0, v___x_2767_);
v___x_2769_ = v___x_2760_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(3, 1, 0);
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
default: 
{
lean_object* v_autoImplicits_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2787_; 
v_autoImplicits_2772_ = lean_ctor_get(v_ctx_2756_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_ctx_2756_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2774_ = v_ctx_2756_;
v_isShared_2775_ = v_isSharedCheck_2787_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_autoImplicits_2772_);
lean_dec(v_ctx_2756_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2787_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2776_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2777_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2778_ = lean_array_to_list(v_autoImplicits_2772_);
v___x_2779_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2778_);
lean_dec(v___x_2778_);
v___x_2780_ = lean_string_append(v___x_2777_, v___x_2779_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = lean_string_append(v___x_2776_, v___x_2780_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_2783_ = lean_string_append(v___x_2781_, v___x_2782_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 3);
lean_ctor_set(v___x_2774_, 0, v___x_2783_);
v___x_2785_ = v___x_2774_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2797_, lean_object* v_ctx_x3f_2798_){
_start:
{
switch(lean_obj_tag(v_tree_2797_))
{
case 0:
{
lean_object* v_i_2800_; lean_object* v_t_2801_; lean_object* v___x_2802_; 
v_i_2800_ = lean_ctor_get(v_tree_2797_, 0);
lean_inc_ref(v_i_2800_);
v_t_2801_ = lean_ctor_get(v_tree_2797_, 1);
lean_inc_ref(v_t_2801_);
lean_dec_ref(v_tree_2797_);
v___x_2802_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2800_, v_ctx_x3f_2798_);
v_tree_2797_ = v_t_2801_;
v_ctx_x3f_2798_ = v___x_2802_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2798_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec_ref(v_tree_2797_);
v___x_2804_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
else
{
lean_object* v_i_2806_; lean_object* v_children_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2857_; 
v_i_2806_ = lean_ctor_get(v_tree_2797_, 0);
v_children_2807_ = lean_ctor_get(v_tree_2797_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_tree_2797_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2809_ = v_tree_2797_;
v_isShared_2810_ = v_isSharedCheck_2857_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_children_2807_);
lean_inc(v_i_2806_);
lean_dec(v_tree_2797_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2857_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_val_2811_; lean_object* v___x_2812_; 
v_val_2811_ = lean_ctor_get(v_ctx_x3f_2798_, 0);
lean_inc_ref(v_i_2806_);
lean_inc(v_val_2811_);
v___x_2812_ = l_Lean_Elab_Info_format(v_val_2811_, v_i_2806_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2856_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2856_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2856_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_size_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_size_2817_ = lean_ctor_get(v_children_2807_, 2);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_nat_dec_eq(v_size_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_del_object(v___x_2815_);
v___x_2820_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2798_, v_i_2806_);
lean_dec_ref(v_i_2806_);
v___x_2821_ = l_Lean_PersistentArray_toList___redArg(v_children_2807_);
lean_dec_ref(v_children_2807_);
v___x_2822_ = lean_box(0);
v___x_2823_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2820_, v___x_2821_, v___x_2822_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2839_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2839_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2839_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 5);
lean_ctor_set(v___x_2809_, 1, v_a_2813_);
lean_ctor_set(v___x_2809_, 0, v___x_2828_);
v___x_2830_ = v___x_2809_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2813_);
v___x_2830_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2831_ = lean_box(1);
v___x_2832_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2831_, v_a_2824_);
v___x_2833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2830_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Std_Format_nestD(v___x_2833_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2834_);
v___x_2836_ = v___x_2826_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
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
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2813_);
lean_del_object(v___x_2809_);
v_a_2840_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2823_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2823_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_dec_ref(v_children_2807_);
lean_dec_ref(v_ctx_x3f_2798_);
lean_dec_ref(v_i_2806_);
v___x_2848_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 5);
lean_ctor_set(v___x_2809_, 1, v_a_2813_);
lean_ctor_set(v___x_2809_, 0, v___x_2848_);
v___x_2850_ = v___x_2809_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_a_2813_);
v___x_2850_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = l_Std_Format_nestD(v___x_2850_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2851_);
v___x_2853_ = v___x_2815_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
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
}
else
{
lean_del_object(v___x_2809_);
lean_dec_ref(v_children_2807_);
lean_dec_ref(v_ctx_x3f_2798_);
lean_dec_ref(v_i_2806_);
return v___x_2812_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_ctx_x3f_2798_);
v_mvarId_2858_ = lean_ctor_get(v_tree_2797_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_tree_2797_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2860_ = v_tree_2797_;
v_isShared_2861_ = v_isSharedCheck_2871_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_mvarId_2858_);
lean_dec(v_tree_2797_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2871_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2862_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2863_ = 1;
v___x_2864_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2858_, v___x_2863_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 3);
lean_ctor_set(v___x_2860_, 0, v___x_2864_);
v___x_2866_ = v___x_2860_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2862_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Std_Format_nestD(v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2872_, lean_object* v_x_2873_, lean_object* v_x_2874_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v___x_2872_);
v___x_2876_ = l_List_reverse___redArg(v_x_2874_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v_head_2878_; lean_object* v_tail_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2897_; 
v_head_2878_ = lean_ctor_get(v_x_2873_, 0);
v_tail_2879_ = lean_ctor_get(v_x_2873_, 1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2881_ = v_x_2873_;
v_isShared_2882_ = v_isSharedCheck_2897_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_tail_2879_);
lean_inc(v_head_2878_);
lean_dec(v_x_2873_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2897_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; 
lean_inc(v___x_2872_);
v___x_2883_ = l_Lean_Elab_InfoTree_format(v_head_2878_, v___x_2872_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2886_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v_x_2874_);
lean_ctor_set(v___x_2881_, 0, v_a_2884_);
v___x_2886_ = v___x_2881_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2884_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_x_2874_);
v___x_2886_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
v_x_2873_ = v_tail_2879_;
v_x_2874_ = v___x_2886_;
goto _start;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_del_object(v___x_2881_);
lean_dec(v_tail_2879_);
lean_dec(v_x_2874_);
lean_dec(v___x_2872_);
v_a_2889_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2883_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2883_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2898_, v_x_2899_, v_x_2900_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2903_, lean_object* v_ctx_x3f_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Elab_InfoTree_format(v_tree_2903_, v_ctx_x3f_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2907_, lean_object* v_s_2908_){
_start:
{
uint8_t v_enabled_2909_; lean_object* v_assignment_2910_; lean_object* v_lazyAssignment_2911_; lean_object* v_trees_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_enabled_2909_ = lean_ctor_get_uint8(v_s_2908_, sizeof(void*)*3);
v_assignment_2910_ = lean_ctor_get(v_s_2908_, 0);
v_lazyAssignment_2911_ = lean_ctor_get(v_s_2908_, 1);
v_trees_2912_ = lean_ctor_get(v_s_2908_, 2);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_s_2908_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v_s_2908_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_trees_2912_);
lean_inc(v_lazyAssignment_2911_);
lean_inc(v_assignment_2910_);
lean_dec(v_s_2908_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_apply_1(v_f_2907_, v_trees_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 2, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_assignment_2910_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_lazyAssignment_2911_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v___x_2916_);
lean_ctor_set_uint8(v_reuseFailAlloc_2919_, sizeof(void*)*3, v_enabled_2909_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2921_, lean_object* v_f_2922_){
_start:
{
lean_object* v_modifyInfoState_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; 
v_modifyInfoState_2923_ = lean_ctor_get(v_inst_2921_, 1);
lean_inc(v_modifyInfoState_2923_);
lean_dec_ref(v_inst_2921_);
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2924_, 0, v_f_2922_);
v___x_2925_ = lean_apply_1(v_modifyInfoState_2923_, v___f_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2926_, lean_object* v_inst_2927_, lean_object* v_f_2928_){
_start:
{
lean_object* v_modifyInfoState_2929_; lean_object* v___f_2930_; lean_object* v___x_2931_; 
v_modifyInfoState_2929_ = lean_ctor_get(v_inst_2927_, 1);
lean_inc(v_modifyInfoState_2929_);
lean_dec_ref(v_inst_2927_);
v___f_2930_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2930_, 0, v_f_2928_);
v___x_2931_ = lean_apply_1(v_modifyInfoState_2929_, v___f_2930_);
return v___x_2931_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_unsigned_to_nat(32u);
v___x_2933_ = lean_mk_empty_array_with_capacity(v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2935_ = ((size_t)5ULL);
v___x_2936_ = lean_unsigned_to_nat(0u);
v___x_2937_ = lean_unsigned_to_nat(32u);
v___x_2938_ = lean_mk_empty_array_with_capacity(v___x_2937_);
v___x_2939_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2940_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2938_);
lean_ctor_set(v___x_2940_, 2, v___x_2936_);
lean_ctor_set(v___x_2940_, 3, v___x_2936_);
lean_ctor_set_usize(v___x_2940_, 4, v___x_2935_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2941_){
_start:
{
uint8_t v_enabled_2942_; lean_object* v_assignment_2943_; lean_object* v_lazyAssignment_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
v_enabled_2942_ = lean_ctor_get_uint8(v_s_2941_, sizeof(void*)*3);
v_assignment_2943_ = lean_ctor_get(v_s_2941_, 0);
v_lazyAssignment_2944_ = lean_ctor_get(v_s_2941_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_s_2941_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_s_2941_, 2);
lean_dec(v_unused_2953_);
v___x_2946_ = v_s_2941_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_lazyAssignment_2944_);
lean_inc(v_assignment_2943_);
lean_dec(v_s_2941_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_assignment_2943_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_lazyAssignment_2944_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v___x_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2951_, sizeof(void*)*3, v_enabled_2942_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2954_, lean_object* v_trees_2955_, lean_object* v_____r_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_apply_2(v_toPure_2954_, lean_box(0), v_trees_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2958_, lean_object* v_modifyInfoState_2959_, lean_object* v___f_2960_, lean_object* v_toBind_2961_, lean_object* v_____do__lift_2962_){
_start:
{
lean_object* v_trees_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_trees_2963_ = lean_ctor_get(v_____do__lift_2962_, 2);
lean_inc_ref(v_trees_2963_);
lean_dec_ref(v_____do__lift_2962_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2964_, 0, v_toPure_2958_);
lean_closure_set(v___f_2964_, 1, v_trees_2963_);
v___x_2965_ = lean_apply_1(v_modifyInfoState_2959_, v___f_2960_);
v___x_2966_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v___x_2965_, v___f_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2968_, lean_object* v_inst_2969_){
_start:
{
lean_object* v_toApplicative_2970_; lean_object* v_toBind_2971_; lean_object* v_getInfoState_2972_; lean_object* v_modifyInfoState_2973_; lean_object* v_toPure_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; 
v_toApplicative_2970_ = lean_ctor_get(v_inst_2968_, 0);
lean_inc_ref(v_toApplicative_2970_);
v_toBind_2971_ = lean_ctor_get(v_inst_2968_, 1);
lean_inc_n(v_toBind_2971_, 2);
lean_dec_ref(v_inst_2968_);
v_getInfoState_2972_ = lean_ctor_get(v_inst_2969_, 0);
lean_inc(v_getInfoState_2972_);
v_modifyInfoState_2973_ = lean_ctor_get(v_inst_2969_, 1);
lean_inc(v_modifyInfoState_2973_);
lean_dec_ref(v_inst_2969_);
v_toPure_2974_ = lean_ctor_get(v_toApplicative_2970_, 1);
lean_inc(v_toPure_2974_);
lean_dec_ref(v_toApplicative_2970_);
v___f_2975_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2976_, 0, v_toPure_2974_);
lean_closure_set(v___f_2976_, 1, v_modifyInfoState_2973_);
lean_closure_set(v___f_2976_, 2, v___f_2975_);
lean_closure_set(v___f_2976_, 3, v_toBind_2971_);
v___x_2977_ = lean_apply_4(v_toBind_2971_, lean_box(0), lean_box(0), v_getInfoState_2972_, v___f_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2979_, v_inst_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2982_, lean_object* v_s_2983_){
_start:
{
uint8_t v_enabled_2984_; lean_object* v_assignment_2985_; lean_object* v_lazyAssignment_2986_; lean_object* v_trees_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
v_enabled_2984_ = lean_ctor_get_uint8(v_s_2983_, sizeof(void*)*3);
v_assignment_2985_ = lean_ctor_get(v_s_2983_, 0);
v_lazyAssignment_2986_ = lean_ctor_get(v_s_2983_, 1);
v_trees_2987_ = lean_ctor_get(v_s_2983_, 2);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_s_2983_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2989_ = v_s_2983_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_trees_2987_);
lean_inc(v_lazyAssignment_2986_);
lean_inc(v_assignment_2985_);
lean_dec(v_s_2983_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = l_Lean_PersistentArray_push___redArg(v_trees_2987_, v_t_2982_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 2, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_assignment_2985_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_lazyAssignment_2986_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v___x_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2994_, sizeof(void*)*3, v_enabled_2984_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2996_, lean_object* v_modifyInfoState_2997_, lean_object* v___f_2998_, lean_object* v_____do__lift_2999_){
_start:
{
uint8_t v_enabled_3000_; 
v_enabled_3000_ = lean_ctor_get_uint8(v_____do__lift_2999_, sizeof(void*)*3);
if (v_enabled_3000_ == 0)
{
lean_object* v_toPure_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v___f_2998_);
lean_dec(v_modifyInfoState_2997_);
v_toPure_3001_ = lean_ctor_get(v_toApplicative_2996_, 1);
lean_inc(v_toPure_3001_);
lean_dec_ref(v_toApplicative_2996_);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3002_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref(v_toApplicative_2996_);
v___x_3004_ = lean_apply_1(v_modifyInfoState_2997_, v___f_2998_);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_3005_, lean_object* v_modifyInfoState_3006_, lean_object* v___f_3007_, lean_object* v_____do__lift_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_3005_, v_modifyInfoState_3006_, v___f_3007_, v_____do__lift_3008_);
lean_dec_ref(v_____do__lift_3008_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_t_3012_){
_start:
{
lean_object* v_toApplicative_3013_; lean_object* v_toBind_3014_; lean_object* v_getInfoState_3015_; lean_object* v_modifyInfoState_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; 
v_toApplicative_3013_ = lean_ctor_get(v_inst_3010_, 0);
lean_inc_ref(v_toApplicative_3013_);
v_toBind_3014_ = lean_ctor_get(v_inst_3010_, 1);
lean_inc(v_toBind_3014_);
lean_dec_ref(v_inst_3010_);
v_getInfoState_3015_ = lean_ctor_get(v_inst_3011_, 0);
lean_inc(v_getInfoState_3015_);
v_modifyInfoState_3016_ = lean_ctor_get(v_inst_3011_, 1);
lean_inc(v_modifyInfoState_3016_);
lean_dec_ref(v_inst_3011_);
v___f_3017_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3017_, 0, v_t_3012_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3018_, 0, v_toApplicative_3013_);
lean_closure_set(v___f_3018_, 1, v_modifyInfoState_3016_);
lean_closure_set(v___f_3018_, 2, v___f_3017_);
v___x_3019_ = lean_apply_4(v_toBind_3014_, lean_box(0), lean_box(0), v_getInfoState_3015_, v___f_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_t_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3021_, v_inst_3022_, v_t_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_3025_, lean_object* v_t_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_____do__lift_3029_){
_start:
{
uint8_t v_enabled_3030_; 
v_enabled_3030_ = lean_ctor_get_uint8(v_____do__lift_3029_, sizeof(void*)*3);
if (v_enabled_3030_ == 0)
{
lean_object* v_toPure_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v_inst_3028_);
lean_dec_ref(v_inst_3027_);
lean_dec_ref(v_t_3026_);
v_toPure_3031_ = lean_ctor_get(v_toApplicative_3025_, 1);
lean_inc(v_toPure_3031_);
lean_dec_ref(v_toApplicative_3025_);
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_apply_2(v_toPure_3031_, lean_box(0), v___x_3032_);
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref(v_toApplicative_3025_);
v___x_3034_ = lean_unsigned_to_nat(32u);
v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
lean_dec_ref(v___x_3035_);
v___x_3036_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_t_3026_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_3027_, v_inst_3028_, v___x_3037_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_3039_, lean_object* v_t_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_____do__lift_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_3039_, v_t_3040_, v_inst_3041_, v_inst_3042_, v_____do__lift_3043_);
lean_dec_ref(v_____do__lift_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_t_3047_){
_start:
{
lean_object* v_toApplicative_3048_; lean_object* v_toBind_3049_; lean_object* v_getInfoState_3050_; lean_object* v___f_3051_; lean_object* v___x_3052_; 
v_toApplicative_3048_ = lean_ctor_get(v_inst_3045_, 0);
lean_inc_ref(v_toApplicative_3048_);
v_toBind_3049_ = lean_ctor_get(v_inst_3045_, 1);
lean_inc(v_toBind_3049_);
v_getInfoState_3050_ = lean_ctor_get(v_inst_3046_, 0);
lean_inc(v_getInfoState_3050_);
v___f_3051_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3051_, 0, v_toApplicative_3048_);
lean_closure_set(v___f_3051_, 1, v_t_3047_);
lean_closure_set(v___f_3051_, 2, v_inst_3045_);
lean_closure_set(v___f_3051_, 3, v_inst_3046_);
v___x_3052_ = lean_apply_4(v_toBind_3049_, lean_box(0), lean_box(0), v_getInfoState_3050_, v___f_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_t_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3054_, v_inst_3055_, v_t_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_info_3060_){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_info_3060_);
v___x_3062_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3058_, v_inst_3059_, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v_info_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3064_, v_inst_3065_, v_info_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3068_, lean_object* v_expectedType_x3f_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_____do__lift_3072_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3073_ = lean_box(0);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v_stx_3068_);
v___x_3075_ = l_Lean_LocalContext_empty;
v___x_3076_ = 0;
v___x_3077_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3077_, 0, v___x_3074_);
lean_ctor_set(v___x_3077_, 1, v___x_3075_);
lean_ctor_set(v___x_3077_, 2, v_expectedType_x3f_3069_);
lean_ctor_set(v___x_3077_, 3, v_____do__lift_3072_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*4, v___x_3076_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*4 + 1, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
v___x_3079_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3070_, v_inst_3071_, v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_stx_3084_, lean_object* v_n_3085_, lean_object* v_expectedType_x3f_3086_){
_start:
{
lean_object* v_toBind_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_toBind_3087_ = lean_ctor_get(v_inst_3080_, 1);
lean_inc(v_toBind_3087_);
lean_inc_ref(v_inst_3080_);
v___f_3088_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3088_, 0, v_stx_3084_);
lean_closure_set(v___f_3088_, 1, v_expectedType_x3f_3086_);
lean_closure_set(v___f_3088_, 2, v_inst_3080_);
lean_closure_set(v___f_3088_, 3, v_inst_3081_);
v___x_3089_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3080_, v_inst_3082_, v_inst_3083_, v_n_3085_);
v___x_3090_ = lean_apply_4(v_toBind_3087_, lean_box(0), lean_box(0), v___x_3089_, v___f_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_inst_3095_, lean_object* v_stx_3096_, lean_object* v_n_3097_, lean_object* v_expectedType_x3f_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3092_, v_inst_3093_, v_inst_3094_, v_inst_3095_, v_stx_3096_, v_n_3097_, v_expectedType_x3f_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v_infoState_3104_; uint8_t v_enabled_3105_; 
v___x_3103_ = lean_st_ref_get(v___y_3101_);
v_infoState_3104_ = lean_ctor_get(v___x_3103_, 7);
lean_inc_ref(v_infoState_3104_);
lean_dec(v___x_3103_);
v_enabled_3105_ = lean_ctor_get_uint8(v_infoState_3104_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3104_);
if (v_enabled_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec_ref(v_t_3100_);
v___x_3106_ = lean_box(0);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; lean_object* v_infoState_3109_; lean_object* v_env_3110_; lean_object* v_nextMacroScope_3111_; lean_object* v_ngen_3112_; lean_object* v_auxDeclNGen_3113_; lean_object* v_traceState_3114_; lean_object* v_cache_3115_; lean_object* v_messages_3116_; lean_object* v_snapshotTasks_3117_; lean_object* v_newDecls_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3140_; 
v___x_3108_ = lean_st_ref_take(v___y_3101_);
v_infoState_3109_ = lean_ctor_get(v___x_3108_, 7);
v_env_3110_ = lean_ctor_get(v___x_3108_, 0);
v_nextMacroScope_3111_ = lean_ctor_get(v___x_3108_, 1);
v_ngen_3112_ = lean_ctor_get(v___x_3108_, 2);
v_auxDeclNGen_3113_ = lean_ctor_get(v___x_3108_, 3);
v_traceState_3114_ = lean_ctor_get(v___x_3108_, 4);
v_cache_3115_ = lean_ctor_get(v___x_3108_, 5);
v_messages_3116_ = lean_ctor_get(v___x_3108_, 6);
v_snapshotTasks_3117_ = lean_ctor_get(v___x_3108_, 8);
v_newDecls_3118_ = lean_ctor_get(v___x_3108_, 9);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3120_ = v___x_3108_;
v_isShared_3121_ = v_isSharedCheck_3140_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_newDecls_3118_);
lean_inc(v_snapshotTasks_3117_);
lean_inc(v_infoState_3109_);
lean_inc(v_messages_3116_);
lean_inc(v_cache_3115_);
lean_inc(v_traceState_3114_);
lean_inc(v_auxDeclNGen_3113_);
lean_inc(v_ngen_3112_);
lean_inc(v_nextMacroScope_3111_);
lean_inc(v_env_3110_);
lean_dec(v___x_3108_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3140_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
uint8_t v_enabled_3122_; lean_object* v_assignment_3123_; lean_object* v_lazyAssignment_3124_; lean_object* v_trees_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3139_; 
v_enabled_3122_ = lean_ctor_get_uint8(v_infoState_3109_, sizeof(void*)*3);
v_assignment_3123_ = lean_ctor_get(v_infoState_3109_, 0);
v_lazyAssignment_3124_ = lean_ctor_get(v_infoState_3109_, 1);
v_trees_3125_ = lean_ctor_get(v_infoState_3109_, 2);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_infoState_3109_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3127_ = v_infoState_3109_;
v_isShared_3128_ = v_isSharedCheck_3139_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_trees_3125_);
lean_inc(v_lazyAssignment_3124_);
lean_inc(v_assignment_3123_);
lean_dec(v_infoState_3109_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3139_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = l_Lean_PersistentArray_push___redArg(v_trees_3125_, v_t_3100_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 2, v___x_3129_);
v___x_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_assignment_3123_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_lazyAssignment_3124_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v___x_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3138_, sizeof(void*)*3, v_enabled_3122_);
v___x_3131_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3133_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 7, v___x_3131_);
v___x_3133_ = v___x_3120_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_env_3110_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_nextMacroScope_3111_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_ngen_3112_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_auxDeclNGen_3113_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_traceState_3114_);
lean_ctor_set(v_reuseFailAlloc_3137_, 5, v_cache_3115_);
lean_ctor_set(v_reuseFailAlloc_3137_, 6, v_messages_3116_);
lean_ctor_set(v_reuseFailAlloc_3137_, 7, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3137_, 8, v_snapshotTasks_3117_);
lean_ctor_set(v_reuseFailAlloc_3137_, 9, v_newDecls_3118_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_st_ref_set(v___y_3101_, v___x_3133_);
v___x_3135_ = lean_box(0);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3141_, v___y_3142_);
lean_dec(v___y_3142_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v_infoState_3150_; uint8_t v_enabled_3151_; 
v___x_3149_ = lean_st_ref_get(v___y_3147_);
v_infoState_3150_ = lean_ctor_get(v___x_3149_, 7);
lean_inc_ref(v_infoState_3150_);
lean_dec(v___x_3149_);
v_enabled_3151_ = lean_ctor_get_uint8(v_infoState_3150_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3150_);
if (v_enabled_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec_ref(v_t_3145_);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3154_ = lean_unsigned_to_nat(32u);
v___x_3155_ = lean_mk_empty_array_with_capacity(v___x_3154_);
lean_dec_ref(v___x_3155_);
v___x_3156_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_t_3145_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3157_, v___y_3147_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
lean_ctor_set(v___x_3169_, 2, v___x_3168_);
lean_ctor_set(v___x_3169_, 3, v___x_3168_);
lean_ctor_set(v___x_3169_, 4, v___x_3167_);
lean_ctor_set(v___x_3169_, 5, v___x_3167_);
lean_ctor_set(v___x_3169_, 6, v___x_3167_);
lean_ctor_set(v___x_3169_, 7, v___x_3167_);
lean_ctor_set(v___x_3169_, 8, v___x_3167_);
lean_ctor_set(v___x_3169_, 9, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3170_ = lean_box(1);
v___x_3171_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3170_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3179_ = l_Lean_stringToMessageData(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3195_, lean_object* v_declHint_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v_env_3200_; uint8_t v___x_3201_; 
v___x_3199_ = lean_st_ref_get(v___y_3197_);
v_env_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3199_);
v___x_3201_ = l_Lean_Name_isAnonymous(v_declHint_3196_);
if (v___x_3201_ == 0)
{
uint8_t v_isExporting_3202_; 
v_isExporting_3202_ = lean_ctor_get_uint8(v_env_3200_, sizeof(void*)*8);
if (v_isExporting_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_msg_3195_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; uint8_t v___x_3205_; 
lean_inc_ref(v_env_3200_);
v___x_3204_ = l_Lean_Environment_setExporting(v_env_3200_, v___x_3201_);
lean_inc(v_declHint_3196_);
lean_inc_ref(v___x_3204_);
v___x_3205_ = l_Lean_Environment_contains(v___x_3204_, v_declHint_3196_, v_isExporting_3202_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v___x_3204_);
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_msg_3195_);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_c_3212_; lean_object* v___x_3213_; 
v___x_3207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3209_ = l_Lean_Options_empty;
v___x_3210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3204_);
lean_ctor_set(v___x_3210_, 1, v___x_3207_);
lean_ctor_set(v___x_3210_, 2, v___x_3208_);
lean_ctor_set(v___x_3210_, 3, v___x_3209_);
lean_inc(v_declHint_3196_);
v___x_3211_ = l_Lean_MessageData_ofConstName(v_declHint_3196_, v___x_3201_);
v_c_3212_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3212_, 0, v___x_3210_);
lean_ctor_set(v_c_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3200_, v_declHint_3196_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v_c_3212_);
v___x_3216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3215_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Lean_MessageData_note(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_msg_3195_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3256_; 
v_val_3221_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3223_ = v___x_3213_;
v_isShared_3224_ = v_isSharedCheck_3256_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_val_3221_);
lean_dec(v___x_3213_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3256_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_mod_3228_; uint8_t v___x_3229_; 
v___x_3225_ = lean_box(0);
v___x_3226_ = l_Lean_Environment_header(v_env_3200_);
lean_dec_ref(v_env_3200_);
v___x_3227_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3226_);
v_mod_3228_ = lean_array_get(v___x_3225_, v___x_3227_, v_val_3221_);
lean_dec(v_val_3221_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = l_Lean_isPrivateName(v_declHint_3196_);
lean_dec(v_declHint_3196_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v_c_3212_);
v___x_3232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_MessageData_ofName(v_mod_3228_);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_MessageData_note(v___x_3237_);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_msg_3195_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3239_);
v___x_3241_ = v___x_3223_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v_c_3212_);
v___x_3245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_MessageData_ofName(v_mod_3228_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_MessageData_note(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_msg_3195_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3252_);
v___x_3254_ = v___x_3223_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3257_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_msg_3195_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3258_, lean_object* v_declHint_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3258_, v_declHint_3259_, v___y_3260_);
lean_dec(v___y_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3263_, lean_object* v_declHint_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3278_; 
v___x_3268_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3263_, v_declHint_3264_, v___y_3266_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3273_ = l_Lean_unknownIdentifierMessageTag;
v___x_3274_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v_a_3269_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3274_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3279_, lean_object* v_declHint_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3279_, v_declHint_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v_env_3290_; lean_object* v_options_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3289_ = lean_st_ref_get(v___y_3287_);
v_env_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc_ref(v_env_3290_);
lean_dec(v___x_3289_);
v_options_3291_ = lean_ctor_get(v___y_3286_, 2);
v___x_3292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3293_ = lean_unsigned_to_nat(32u);
v___x_3294_ = lean_mk_empty_array_with_capacity(v___x_3293_);
lean_dec_ref(v___x_3294_);
v___x_3295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3291_);
v___x_3296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3296_, 0, v_env_3290_);
lean_ctor_set(v___x_3296_, 1, v___x_3292_);
lean_ctor_set(v___x_3296_, 2, v___x_3295_);
lean_ctor_set(v___x_3296_, 3, v_options_3291_);
v___x_3297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v_msgData_3285_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_ref_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3318_; 
v_ref_3308_ = lean_ctor_get(v___y_3305_, 5);
v___x_3309_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3304_, v___y_3305_, v___y_3306_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_inc(v_ref_3308_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_ref_3308_);
lean_ctor_set(v___x_3314_, 1, v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 1);
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_fileName_3329_; lean_object* v_fileMap_3330_; lean_object* v_options_3331_; lean_object* v_currRecDepth_3332_; lean_object* v_maxRecDepth_3333_; lean_object* v_ref_3334_; lean_object* v_currNamespace_3335_; lean_object* v_openDecls_3336_; lean_object* v_initHeartbeats_3337_; lean_object* v_maxHeartbeats_3338_; lean_object* v_quotContext_3339_; lean_object* v_currMacroScope_3340_; uint8_t v_diag_3341_; lean_object* v_cancelTk_x3f_3342_; uint8_t v_suppressElabErrors_3343_; lean_object* v_inheritedTraceOptions_3344_; lean_object* v_ref_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_fileName_3329_ = lean_ctor_get(v___y_3326_, 0);
v_fileMap_3330_ = lean_ctor_get(v___y_3326_, 1);
v_options_3331_ = lean_ctor_get(v___y_3326_, 2);
v_currRecDepth_3332_ = lean_ctor_get(v___y_3326_, 3);
v_maxRecDepth_3333_ = lean_ctor_get(v___y_3326_, 4);
v_ref_3334_ = lean_ctor_get(v___y_3326_, 5);
v_currNamespace_3335_ = lean_ctor_get(v___y_3326_, 6);
v_openDecls_3336_ = lean_ctor_get(v___y_3326_, 7);
v_initHeartbeats_3337_ = lean_ctor_get(v___y_3326_, 8);
v_maxHeartbeats_3338_ = lean_ctor_get(v___y_3326_, 9);
v_quotContext_3339_ = lean_ctor_get(v___y_3326_, 10);
v_currMacroScope_3340_ = lean_ctor_get(v___y_3326_, 11);
v_diag_3341_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*14);
v_cancelTk_x3f_3342_ = lean_ctor_get(v___y_3326_, 12);
v_suppressElabErrors_3343_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3344_ = lean_ctor_get(v___y_3326_, 13);
v_ref_3345_ = l_Lean_replaceRef(v_ref_3324_, v_ref_3334_);
lean_inc_ref(v_inheritedTraceOptions_3344_);
lean_inc(v_cancelTk_x3f_3342_);
lean_inc(v_currMacroScope_3340_);
lean_inc(v_quotContext_3339_);
lean_inc(v_maxHeartbeats_3338_);
lean_inc(v_initHeartbeats_3337_);
lean_inc(v_openDecls_3336_);
lean_inc(v_currNamespace_3335_);
lean_inc(v_maxRecDepth_3333_);
lean_inc(v_currRecDepth_3332_);
lean_inc_ref(v_options_3331_);
lean_inc_ref(v_fileMap_3330_);
lean_inc_ref(v_fileName_3329_);
v___x_3346_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3346_, 0, v_fileName_3329_);
lean_ctor_set(v___x_3346_, 1, v_fileMap_3330_);
lean_ctor_set(v___x_3346_, 2, v_options_3331_);
lean_ctor_set(v___x_3346_, 3, v_currRecDepth_3332_);
lean_ctor_set(v___x_3346_, 4, v_maxRecDepth_3333_);
lean_ctor_set(v___x_3346_, 5, v_ref_3345_);
lean_ctor_set(v___x_3346_, 6, v_currNamespace_3335_);
lean_ctor_set(v___x_3346_, 7, v_openDecls_3336_);
lean_ctor_set(v___x_3346_, 8, v_initHeartbeats_3337_);
lean_ctor_set(v___x_3346_, 9, v_maxHeartbeats_3338_);
lean_ctor_set(v___x_3346_, 10, v_quotContext_3339_);
lean_ctor_set(v___x_3346_, 11, v_currMacroScope_3340_);
lean_ctor_set(v___x_3346_, 12, v_cancelTk_x3f_3342_);
lean_ctor_set(v___x_3346_, 13, v_inheritedTraceOptions_3344_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*14, v_diag_3341_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*14 + 1, v_suppressElabErrors_3343_);
v___x_3347_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3325_, v___x_3346_, v___y_3327_);
lean_dec_ref(v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3348_, lean_object* v_msg_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3348_, v_msg_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v_ref_3348_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3354_, lean_object* v_msg_3355_, lean_object* v_declHint_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3362_; 
v___x_3360_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3355_, v_declHint_3356_, v___y_3357_, v___y_3358_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3354_, v_a_3361_, v___y_3357_, v___y_3358_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3363_, lean_object* v_msg_3364_, lean_object* v_declHint_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3363_, v_msg_3364_, v_declHint_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v_ref_3363_);
return v_res_3369_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3375_ = l_Lean_stringToMessageData(v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3376_, lean_object* v_constName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3381_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3382_ = 0;
lean_inc(v_constName_3377_);
v___x_3383_ = l_Lean_MessageData_ofConstName(v_constName_3377_, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3381_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3376_, v___x_3386_, v_constName_3377_, v___y_3378_, v___y_3379_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3388_, lean_object* v_constName_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3388_, v_constName_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v_ref_3388_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_ref_3398_; lean_object* v___x_3399_; 
v_ref_3398_ = lean_ctor_get(v___y_3395_, 5);
v___x_3399_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3398_, v_constName_3394_, v___y_3395_, v___y_3396_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; lean_object* v_env_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_st_ref_get(v___y_3407_);
v_env_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc_ref(v_env_3410_);
lean_dec(v___x_3409_);
v___x_3411_ = 0;
lean_inc(v_constName_3405_);
v___x_3412_ = l_Lean_Environment_findConstVal_x3f(v_env_3410_, v_constName_3405_, v___x_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3405_, v___y_3406_, v___y_3407_);
return v___x_3413_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v_constName_3405_);
v_val_3414_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3412_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_val_3414_);
lean_dec(v___x_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 0);
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_val_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
if (lean_obj_tag(v_a_3427_) == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = l_List_reverse___redArg(v_a_3428_);
return v___x_3429_;
}
else
{
lean_object* v_head_3430_; lean_object* v_tail_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3440_; 
v_head_3430_ = lean_ctor_get(v_a_3427_, 0);
v_tail_3431_ = lean_ctor_get(v_a_3427_, 1);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_a_3427_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3433_ = v_a_3427_;
v_isShared_3434_ = v_isSharedCheck_3440_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_tail_3431_);
lean_inc(v_head_3430_);
lean_dec(v_a_3427_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3440_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_mkLevelParam(v_head_3430_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v_a_3428_);
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_a_3428_);
v___x_3437_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
v_a_3427_ = v_tail_3431_;
v_a_3428_ = v___x_3437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
lean_inc(v_constName_3441_);
v___x_3445_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3457_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3457_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3457_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_levelParams_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
v_levelParams_3450_ = lean_ctor_get(v_a_3446_, 1);
lean_inc(v_levelParams_3450_);
lean_dec(v_a_3446_);
v___x_3451_ = lean_box(0);
v___x_3452_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3450_, v___x_3451_);
v___x_3453_ = l_Lean_mkConst(v_constName_3441_, v___x_3452_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3453_);
v___x_3455_ = v___x_3448_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_constName_3441_);
v_a_3458_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3445_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3445_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3471_, lean_object* v_n_3472_, lean_object* v_expectedType_x3f_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3472_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = lean_box(0);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v_stx_3471_);
v___x_3481_ = l_Lean_LocalContext_empty;
v___x_3482_ = 0;
v___x_3483_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3483_, 0, v___x_3480_);
lean_ctor_set(v___x_3483_, 1, v___x_3481_);
lean_ctor_set(v___x_3483_, 2, v_expectedType_x3f_3473_);
lean_ctor_set(v___x_3483_, 3, v_a_3478_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*4, v___x_3482_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*4 + 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3484_, v___y_3474_, v___y_3475_);
return v___x_3485_;
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v_expectedType_x3f_3473_);
lean_dec(v_stx_3471_);
v_a_3486_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3477_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3477_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3494_, lean_object* v_n_3495_, lean_object* v_expectedType_x3f_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3494_, v_n_3495_, v_expectedType_x3f_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3501_, lean_object* v_expectedType_x3f_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; 
lean_inc(v_id_3501_);
v___x_3506_ = l_Lean_realizeGlobalConstNoOverload(v_id_3501_, v_a_3503_, v_a_3504_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3534_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3534_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3534_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v_infoState_3512_; uint8_t v_enabled_3513_; 
v___x_3511_ = lean_st_ref_get(v_a_3504_);
v_infoState_3512_ = lean_ctor_get(v___x_3511_, 7);
lean_inc_ref(v_infoState_3512_);
lean_dec(v___x_3511_);
v_enabled_3513_ = lean_ctor_get_uint8(v_infoState_3512_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3512_);
if (v_enabled_3513_ == 0)
{
lean_object* v___x_3515_; 
lean_dec(v_expectedType_x3f_3502_);
lean_dec(v_id_3501_);
if (v_isShared_3510_ == 0)
{
v___x_3515_ = v___x_3509_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3507_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
else
{
lean_object* v___x_3517_; 
lean_del_object(v___x_3509_);
lean_inc(v_a_3507_);
v___x_3517_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3501_, v_a_3507_, v_expectedType_x3f_3502_, v_a_3503_, v_a_3504_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; 
v_unused_3525_ = lean_ctor_get(v___x_3517_, 0);
lean_dec(v_unused_3525_);
v___x_3519_ = v___x_3517_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v___x_3517_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v_a_3507_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3507_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3507_);
v_a_3526_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3517_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3517_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3502_);
lean_dec(v_id_3501_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3535_, lean_object* v_expectedType_x3f_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3535_, v_expectedType_x3f_3536_, v_a_3537_, v_a_3538_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3541_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3551_, lean_object* v_constName_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3552_, v___y_3553_, v___y_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3557_, lean_object* v_constName_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3557_, v_constName_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3563_, lean_object* v_ref_3564_, lean_object* v_constName_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3564_, v_constName_3565_, v___y_3566_, v___y_3567_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3570_, lean_object* v_ref_3571_, lean_object* v_constName_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3570_, v_ref_3571_, v_constName_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v_ref_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3577_, lean_object* v_ref_3578_, lean_object* v_msg_3579_, lean_object* v_declHint_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3578_, v_msg_3579_, v_declHint_3580_, v___y_3581_, v___y_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3585_, lean_object* v_ref_3586_, lean_object* v_msg_3587_, lean_object* v_declHint_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3585_, v_ref_3586_, v_msg_3587_, v_declHint_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v_ref_3586_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3593_, lean_object* v_declHint_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3593_, v_declHint_3594_, v___y_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3599_, lean_object* v_declHint_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3599_, v_declHint_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3605_, lean_object* v_ref_3606_, lean_object* v_msg_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3606_, v_msg_3607_, v___y_3608_, v___y_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3612_, lean_object* v_ref_3613_, lean_object* v_msg_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3612_, v_ref_3613_, v_msg_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v_ref_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3619_, lean_object* v_msg_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3620_, v___y_3621_, v___y_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_msg_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3625_, v_msg_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3631_, lean_object* v_expectedType_x3f_3632_, lean_object* v_as_x27_3633_, lean_object* v_b_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
if (lean_obj_tag(v_as_x27_3633_) == 0)
{
lean_object* v___x_3638_; 
lean_dec(v_expectedType_x3f_3632_);
lean_dec(v_id_3631_);
v___x_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_b_3634_);
return v___x_3638_;
}
else
{
lean_object* v_head_3639_; lean_object* v_tail_3640_; lean_object* v___x_3641_; 
v_head_3639_ = lean_ctor_get(v_as_x27_3633_, 0);
v_tail_3640_ = lean_ctor_get(v_as_x27_3633_, 1);
lean_inc(v_expectedType_x3f_3632_);
lean_inc(v_head_3639_);
lean_inc(v_id_3631_);
v___x_3641_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3631_, v_head_3639_, v_expectedType_x3f_3632_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; 
lean_dec_ref(v___x_3641_);
v___x_3642_ = lean_box(0);
v_as_x27_3633_ = v_tail_3640_;
v_b_3634_ = v___x_3642_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_3632_);
lean_dec(v_id_3631_);
return v___x_3641_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3644_, lean_object* v_expectedType_x3f_3645_, lean_object* v_as_x27_3646_, lean_object* v_b_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3644_, v_expectedType_x3f_3645_, v_as_x27_3646_, v_b_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v_as_x27_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3652_, lean_object* v_expectedType_x3f_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v___x_3657_; 
lean_inc(v_id_3652_);
v___x_3657_ = l_Lean_realizeGlobalConst(v_id_3652_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3686_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3686_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3686_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v_infoState_3663_; uint8_t v_enabled_3664_; 
v___x_3662_ = lean_st_ref_get(v_a_3655_);
v_infoState_3663_ = lean_ctor_get(v___x_3662_, 7);
lean_inc_ref(v_infoState_3663_);
lean_dec(v___x_3662_);
v_enabled_3664_ = lean_ctor_get_uint8(v_infoState_3663_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3663_);
if (v_enabled_3664_ == 0)
{
lean_object* v___x_3666_; 
lean_dec(v_expectedType_x3f_3653_);
lean_dec(v_id_3652_);
if (v_isShared_3661_ == 0)
{
v___x_3666_ = v___x_3660_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3658_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_del_object(v___x_3660_);
v___x_3668_ = lean_box(0);
v___x_3669_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3652_, v_expectedType_x3f_3653_, v_a_3658_, v___x_3668_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v___x_3669_, 0);
lean_dec(v_unused_3677_);
v___x_3671_ = v___x_3669_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_dec(v___x_3669_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v_a_3658_);
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3658_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_a_3658_);
v_a_3678_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3669_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3669_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3653_);
lean_dec(v_id_3652_);
return v___x_3657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3687_, lean_object* v_expectedType_x3f_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3687_, v_expectedType_x3f_3688_, v_a_3689_, v_a_3690_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3693_, lean_object* v_expectedType_x3f_3694_, lean_object* v_as_3695_, lean_object* v_as_x27_3696_, lean_object* v_b_3697_, lean_object* v_a_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3693_, v_expectedType_x3f_3694_, v_as_x27_3696_, v_b_3697_, v___y_3699_, v___y_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3703_, lean_object* v_expectedType_x3f_3704_, lean_object* v_as_3705_, lean_object* v_as_x27_3706_, lean_object* v_b_3707_, lean_object* v_a_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3703_, v_expectedType_x3f_3704_, v_as_3705_, v_as_x27_3706_, v_b_3707_, v_a_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v_as_x27_3706_);
lean_dec(v_as_3705_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3713_, lean_object* v_as_x27_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
if (lean_obj_tag(v_as_x27_3714_) == 0)
{
lean_object* v___x_3719_; 
lean_dec(v_ref_3713_);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v_b_3715_);
return v___x_3719_;
}
else
{
lean_object* v_head_3720_; lean_object* v_tail_3721_; lean_object* v_fst_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v_head_3720_ = lean_ctor_get(v_as_x27_3714_, 0);
v_tail_3721_ = lean_ctor_get(v_as_x27_3714_, 1);
v_fst_3722_ = lean_ctor_get(v_head_3720_, 0);
v___x_3723_ = lean_box(0);
lean_inc(v_fst_3722_);
lean_inc(v_ref_3713_);
v___x_3724_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3713_, v_fst_3722_, v___x_3723_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3725_; 
lean_dec_ref(v___x_3724_);
v___x_3725_ = lean_box(0);
v_as_x27_3714_ = v_tail_3721_;
v_b_3715_ = v___x_3725_;
goto _start;
}
else
{
lean_dec(v_ref_3713_);
return v___x_3724_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3727_, lean_object* v_as_x27_3728_, lean_object* v_b_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3727_, v_as_x27_3728_, v_b_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v_as_x27_3728_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3734_, lean_object* v_id_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_realizeGlobalName(v_id_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3768_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3768_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3768_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v_infoState_3745_; uint8_t v_enabled_3746_; 
v___x_3744_ = lean_st_ref_get(v_a_3737_);
v_infoState_3745_ = lean_ctor_get(v___x_3744_, 7);
lean_inc_ref(v_infoState_3745_);
lean_dec(v___x_3744_);
v_enabled_3746_ = lean_ctor_get_uint8(v_infoState_3745_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3745_);
if (v_enabled_3746_ == 0)
{
lean_object* v___x_3748_; 
lean_dec(v_ref_3734_);
if (v_isShared_3743_ == 0)
{
v___x_3748_ = v___x_3742_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3740_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_del_object(v___x_3742_);
v___x_3750_ = lean_box(0);
v___x_3751_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3734_, v_a_3740_, v___x_3750_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v___x_3751_, 0);
lean_dec(v_unused_3759_);
v___x_3753_ = v___x_3751_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_dec(v___x_3751_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v_a_3740_);
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3740_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v_a_3740_);
v_a_3760_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3751_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3751_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_3734_);
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3769_, lean_object* v_id_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3769_, v_id_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3775_, lean_object* v_as_3776_, lean_object* v_as_x27_3777_, lean_object* v_b_3778_, lean_object* v_a_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3775_, v_as_x27_3777_, v_b_3778_, v___y_3780_, v___y_3781_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3784_, lean_object* v_as_3785_, lean_object* v_as_x27_3786_, lean_object* v_b_3787_, lean_object* v_a_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3784_, v_as_3785_, v_as_x27_3786_, v_b_3787_, v_a_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_as_x27_3786_);
lean_dec(v_as_3785_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3793_){
_start:
{
lean_object* v_fst_3794_; 
v_fst_3794_ = lean_ctor_get(v_self_3793_, 0);
lean_inc(v_fst_3794_);
return v_fst_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3795_);
lean_dec_ref(v_self_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3797_, lean_object* v_treesSaved_3798_, lean_object* v_s_3799_){
_start:
{
if (lean_obj_tag(v_info_3797_) == 0)
{
uint8_t v_enabled_3800_; lean_object* v_assignment_3801_; lean_object* v_lazyAssignment_3802_; lean_object* v_trees_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3813_; 
v_enabled_3800_ = lean_ctor_get_uint8(v_s_3799_, sizeof(void*)*3);
v_assignment_3801_ = lean_ctor_get(v_s_3799_, 0);
v_lazyAssignment_3802_ = lean_ctor_get(v_s_3799_, 1);
v_trees_3803_ = lean_ctor_get(v_s_3799_, 2);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_s_3799_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3805_ = v_s_3799_;
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_trees_3803_);
lean_inc(v_lazyAssignment_3802_);
lean_inc(v_assignment_3801_);
lean_dec(v_s_3799_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_val_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v_val_3807_ = lean_ctor_get(v_info_3797_, 0);
lean_inc(v_val_3807_);
lean_dec_ref(v_info_3797_);
v___x_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_val_3807_);
lean_ctor_set(v___x_3808_, 1, v_trees_3803_);
v___x_3809_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3798_, v___x_3808_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 2, v___x_3809_);
v___x_3811_ = v___x_3805_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_assignment_3801_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_lazyAssignment_3802_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v___x_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3812_, sizeof(void*)*3, v_enabled_3800_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
uint8_t v_enabled_3814_; lean_object* v_assignment_3815_; lean_object* v_lazyAssignment_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3832_; 
v_enabled_3814_ = lean_ctor_get_uint8(v_s_3799_, sizeof(void*)*3);
v_assignment_3815_ = lean_ctor_get(v_s_3799_, 0);
v_lazyAssignment_3816_ = lean_ctor_get(v_s_3799_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_s_3799_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_s_3799_, 2);
lean_dec(v_unused_3833_);
v___x_3818_ = v_s_3799_;
v_isShared_3819_ = v_isSharedCheck_3832_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_lazyAssignment_3816_);
lean_inc(v_assignment_3815_);
lean_dec(v_s_3799_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3832_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_val_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3831_; 
v_val_3820_ = lean_ctor_get(v_info_3797_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_info_3797_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3822_ = v_info_3797_;
v_isShared_3823_ = v_isSharedCheck_3831_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_val_3820_);
lean_dec(v_info_3797_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3831_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 2);
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_val_3820_);
v___x_3825_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3798_, v___x_3825_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 2, v___x_3826_);
v___x_3828_ = v___x_3818_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_assignment_3815_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_lazyAssignment_3816_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v___x_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3829_, sizeof(void*)*3, v_enabled_3814_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3834_, lean_object* v_modifyInfoState_3835_, lean_object* v_info_3836_){
_start:
{
lean_object* v___f_3837_; lean_object* v___x_3838_; 
v___f_3837_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3837_, 0, v_info_3836_);
lean_closure_set(v___f_3837_, 1, v_treesSaved_3834_);
v___x_3838_ = lean_apply_1(v_modifyInfoState_3835_, v___f_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3839_, lean_object* v_info_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_apply_1(v___f_3839_, v_info_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3842_, lean_object* v_toBind_3843_, lean_object* v___f_3844_, lean_object* v_____do__lift_3845_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_____do__lift_3845_);
v___x_3847_ = lean_apply_2(v_toPure_3842_, lean_box(0), v___x_3846_);
v___x_3848_ = lean_apply_4(v_toBind_3843_, lean_box(0), lean_box(0), v___x_3847_, v___f_3844_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3849_, lean_object* v_mkInfoOnError_3850_, lean_object* v___f_3851_, lean_object* v_mkInfo_3852_, lean_object* v___f_3853_, lean_object* v_a_x3f_3854_){
_start:
{
if (lean_obj_tag(v_a_x3f_3854_) == 0)
{
lean_object* v___x_3855_; 
lean_dec(v___f_3853_);
lean_dec(v_mkInfo_3852_);
v___x_3855_ = lean_apply_4(v_toBind_3849_, lean_box(0), lean_box(0), v_mkInfoOnError_3850_, v___f_3851_);
return v___x_3855_;
}
else
{
lean_object* v_val_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_dec(v___f_3851_);
lean_dec(v_mkInfoOnError_3850_);
v_val_3856_ = lean_ctor_get(v_a_x3f_3854_, 0);
lean_inc(v_val_3856_);
lean_dec_ref(v_a_x3f_3854_);
v___x_3857_ = lean_apply_1(v_mkInfo_3852_, v_val_3856_);
v___x_3858_ = lean_apply_4(v_toBind_3849_, lean_box(0), lean_box(0), v___x_3857_, v___f_3853_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3859_, lean_object* v_modifyInfoState_3860_, lean_object* v_toBind_3861_, lean_object* v_mkInfoOnError_3862_, lean_object* v_mkInfo_3863_, lean_object* v_inst_3864_, lean_object* v_x_3865_, lean_object* v___f_3866_, lean_object* v_treesSaved_3867_){
_start:
{
lean_object* v_toFunctor_3868_; lean_object* v_toPure_3869_; lean_object* v_map_3870_; lean_object* v___f_3871_; lean_object* v___f_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_toFunctor_3868_ = lean_ctor_get(v_toApplicative_3859_, 0);
lean_inc_ref(v_toFunctor_3868_);
v_toPure_3869_ = lean_ctor_get(v_toApplicative_3859_, 1);
lean_inc(v_toPure_3869_);
lean_dec_ref(v_toApplicative_3859_);
v_map_3870_ = lean_ctor_get(v_toFunctor_3868_, 0);
lean_inc(v_map_3870_);
lean_dec_ref(v_toFunctor_3868_);
v___f_3871_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3871_, 0, v_treesSaved_3867_);
lean_closure_set(v___f_3871_, 1, v_modifyInfoState_3860_);
v___f_3872_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3872_, 0, v___f_3871_);
lean_inc_ref(v___f_3872_);
lean_inc(v_toBind_3861_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3873_, 0, v_toPure_3869_);
lean_closure_set(v___f_3873_, 1, v_toBind_3861_);
lean_closure_set(v___f_3873_, 2, v___f_3872_);
v___f_3874_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3874_, 0, v_toBind_3861_);
lean_closure_set(v___f_3874_, 1, v_mkInfoOnError_3862_);
lean_closure_set(v___f_3874_, 2, v___f_3873_);
lean_closure_set(v___f_3874_, 3, v_mkInfo_3863_);
lean_closure_set(v___f_3874_, 4, v___f_3872_);
v___x_3875_ = lean_apply_4(v_inst_3864_, lean_box(0), lean_box(0), v_x_3865_, v___f_3874_);
v___x_3876_ = lean_apply_4(v_map_3870_, lean_box(0), lean_box(0), v___f_3866_, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3877_, lean_object* v_inst_3878_, lean_object* v_inst_3879_, lean_object* v_toBind_3880_, lean_object* v___f_3881_, lean_object* v_____do__lift_3882_){
_start:
{
uint8_t v_enabled_3883_; 
v_enabled_3883_ = lean_ctor_get_uint8(v_____do__lift_3882_, sizeof(void*)*3);
if (v_enabled_3883_ == 0)
{
lean_dec(v___f_3881_);
lean_dec(v_toBind_3880_);
lean_dec_ref(v_inst_3879_);
lean_dec_ref(v_inst_3878_);
lean_inc(v_x_3877_);
return v_x_3877_;
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3878_, v_inst_3879_);
v___x_3885_ = lean_apply_4(v_toBind_3880_, lean_box(0), lean_box(0), v___x_3884_, v___f_3881_);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3886_, lean_object* v_inst_3887_, lean_object* v_inst_3888_, lean_object* v_toBind_3889_, lean_object* v___f_3890_, lean_object* v_____do__lift_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3886_, v_inst_3887_, v_inst_3888_, v_toBind_3889_, v___f_3890_, v_____do__lift_3891_);
lean_dec_ref(v_____do__lift_3891_);
lean_dec(v_x_3886_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3894_, lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_x_3897_, lean_object* v_mkInfo_3898_, lean_object* v_mkInfoOnError_3899_){
_start:
{
lean_object* v_toApplicative_3900_; lean_object* v_toBind_3901_; lean_object* v_getInfoState_3902_; lean_object* v_modifyInfoState_3903_; lean_object* v___f_3904_; lean_object* v___f_3905_; lean_object* v___f_3906_; lean_object* v___x_3907_; 
v_toApplicative_3900_ = lean_ctor_get(v_inst_3894_, 0);
v_toBind_3901_ = lean_ctor_get(v_inst_3894_, 1);
lean_inc_n(v_toBind_3901_, 3);
v_getInfoState_3902_ = lean_ctor_get(v_inst_3895_, 0);
lean_inc(v_getInfoState_3902_);
v_modifyInfoState_3903_ = lean_ctor_get(v_inst_3895_, 1);
v___f_3904_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3897_);
lean_inc(v_modifyInfoState_3903_);
lean_inc_ref(v_toApplicative_3900_);
v___f_3905_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3905_, 0, v_toApplicative_3900_);
lean_closure_set(v___f_3905_, 1, v_modifyInfoState_3903_);
lean_closure_set(v___f_3905_, 2, v_toBind_3901_);
lean_closure_set(v___f_3905_, 3, v_mkInfoOnError_3899_);
lean_closure_set(v___f_3905_, 4, v_mkInfo_3898_);
lean_closure_set(v___f_3905_, 5, v_inst_3896_);
lean_closure_set(v___f_3905_, 6, v_x_3897_);
lean_closure_set(v___f_3905_, 7, v___f_3904_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3906_, 0, v_x_3897_);
lean_closure_set(v___f_3906_, 1, v_inst_3894_);
lean_closure_set(v___f_3906_, 2, v_inst_3895_);
lean_closure_set(v___f_3906_, 3, v_toBind_3901_);
lean_closure_set(v___f_3906_, 4, v___f_3905_);
v___x_3907_ = lean_apply_4(v_toBind_3901_, lean_box(0), lean_box(0), v_getInfoState_3902_, v___f_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3908_, lean_object* v_inst_3909_, lean_object* v_inst_3910_, lean_object* v_00_u03b1_3911_, lean_object* v_inst_3912_, lean_object* v_x_3913_, lean_object* v_mkInfo_3914_, lean_object* v_mkInfoOnError_3915_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3909_, v_inst_3910_, v_inst_3912_, v_x_3913_, v_mkInfo_3914_, v_mkInfoOnError_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3917_, lean_object* v_tree_3918_, lean_object* v_s_3919_){
_start:
{
uint8_t v_enabled_3920_; lean_object* v_assignment_3921_; lean_object* v_lazyAssignment_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
v_enabled_3920_ = lean_ctor_get_uint8(v_s_3919_, sizeof(void*)*3);
v_assignment_3921_ = lean_ctor_get(v_s_3919_, 0);
v_lazyAssignment_3922_ = lean_ctor_get(v_s_3919_, 1);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_s_3919_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v_s_3919_, 2);
lean_dec(v_unused_3931_);
v___x_3924_ = v_s_3919_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_lazyAssignment_3922_);
lean_inc(v_assignment_3921_);
lean_dec(v_s_3919_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3917_, v_tree_3918_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 2, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_assignment_3921_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_lazyAssignment_3922_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v___x_3926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3929_, sizeof(void*)*3, v_enabled_3920_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3932_, lean_object* v_modifyInfoState_3933_, lean_object* v_tree_3934_){
_start:
{
lean_object* v___f_3935_; lean_object* v___x_3936_; 
v___f_3935_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3935_, 0, v_treesSaved_3932_);
lean_closure_set(v___f_3935_, 1, v_tree_3934_);
v___x_3936_ = lean_apply_1(v_modifyInfoState_3933_, v___f_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3937_, lean_object* v_toBind_3938_, lean_object* v___f_3939_, lean_object* v_st_3940_){
_start:
{
lean_object* v_trees_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_trees_3941_ = lean_ctor_get(v_st_3940_, 2);
lean_inc_ref(v_trees_3941_);
lean_dec_ref(v_st_3940_);
v___x_3942_ = lean_apply_1(v_mkInfoTree_3937_, v_trees_3941_);
v___x_3943_ = lean_apply_4(v_toBind_3938_, lean_box(0), lean_box(0), v___x_3942_, v___f_3939_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3944_, lean_object* v_getInfoState_3945_, lean_object* v___f_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_apply_4(v_toBind_3944_, lean_box(0), lean_box(0), v_getInfoState_3945_, v___f_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3949_, lean_object* v_getInfoState_3950_, lean_object* v___f_3951_, lean_object* v_x_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3949_, v_getInfoState_3950_, v___f_3951_, v_x_3952_);
lean_dec(v_x_3952_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3954_, lean_object* v_modifyInfoState_3955_, lean_object* v_mkInfoTree_3956_, lean_object* v_toBind_3957_, lean_object* v_getInfoState_3958_, lean_object* v_inst_3959_, lean_object* v_x_3960_, lean_object* v___f_3961_, lean_object* v_treesSaved_3962_){
_start:
{
lean_object* v_toFunctor_3963_; lean_object* v_map_3964_; lean_object* v___f_3965_; lean_object* v___f_3966_; lean_object* v___f_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_toFunctor_3963_ = lean_ctor_get(v_toApplicative_3954_, 0);
lean_inc_ref(v_toFunctor_3963_);
lean_dec_ref(v_toApplicative_3954_);
v_map_3964_ = lean_ctor_get(v_toFunctor_3963_, 0);
lean_inc(v_map_3964_);
lean_dec_ref(v_toFunctor_3963_);
v___f_3965_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3965_, 0, v_treesSaved_3962_);
lean_closure_set(v___f_3965_, 1, v_modifyInfoState_3955_);
lean_inc(v_toBind_3957_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3966_, 0, v_mkInfoTree_3956_);
lean_closure_set(v___f_3966_, 1, v_toBind_3957_);
lean_closure_set(v___f_3966_, 2, v___f_3965_);
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3967_, 0, v_toBind_3957_);
lean_closure_set(v___f_3967_, 1, v_getInfoState_3958_);
lean_closure_set(v___f_3967_, 2, v___f_3966_);
v___x_3968_ = lean_apply_4(v_inst_3959_, lean_box(0), lean_box(0), v_x_3960_, v___f_3967_);
v___x_3969_ = lean_apply_4(v_map_3964_, lean_box(0), lean_box(0), v___f_3961_, v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3970_, lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_x_3973_, lean_object* v_mkInfoTree_3974_){
_start:
{
lean_object* v_toApplicative_3975_; lean_object* v_toBind_3976_; lean_object* v_getInfoState_3977_; lean_object* v_modifyInfoState_3978_; lean_object* v___f_3979_; lean_object* v___f_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; 
v_toApplicative_3975_ = lean_ctor_get(v_inst_3970_, 0);
v_toBind_3976_ = lean_ctor_get(v_inst_3970_, 1);
lean_inc_n(v_toBind_3976_, 3);
v_getInfoState_3977_ = lean_ctor_get(v_inst_3971_, 0);
lean_inc_n(v_getInfoState_3977_, 2);
v_modifyInfoState_3978_ = lean_ctor_get(v_inst_3971_, 1);
v___f_3979_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3973_);
lean_inc(v_modifyInfoState_3978_);
lean_inc_ref(v_toApplicative_3975_);
v___f_3980_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3980_, 0, v_toApplicative_3975_);
lean_closure_set(v___f_3980_, 1, v_modifyInfoState_3978_);
lean_closure_set(v___f_3980_, 2, v_mkInfoTree_3974_);
lean_closure_set(v___f_3980_, 3, v_toBind_3976_);
lean_closure_set(v___f_3980_, 4, v_getInfoState_3977_);
lean_closure_set(v___f_3980_, 5, v_inst_3972_);
lean_closure_set(v___f_3980_, 6, v_x_3973_);
lean_closure_set(v___f_3980_, 7, v___f_3979_);
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3981_, 0, v_x_3973_);
lean_closure_set(v___f_3981_, 1, v_inst_3970_);
lean_closure_set(v___f_3981_, 2, v_inst_3971_);
lean_closure_set(v___f_3981_, 3, v_toBind_3976_);
lean_closure_set(v___f_3981_, 4, v___f_3980_);
v___x_3982_ = lean_apply_4(v_toBind_3976_, lean_box(0), lean_box(0), v_getInfoState_3977_, v___f_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3983_, lean_object* v_inst_3984_, lean_object* v_inst_3985_, lean_object* v_00_u03b1_3986_, lean_object* v_inst_3987_, lean_object* v_x_3988_, lean_object* v_mkInfoTree_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3984_, v_inst_3985_, v_inst_3987_, v_x_3988_, v_mkInfoTree_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3991_, lean_object* v_toPure_3992_, lean_object* v_____do__lift_3993_){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3994_, 0, v_____do__lift_3993_);
lean_ctor_set(v___x_3994_, 1, v_trees_3991_);
v___x_3995_ = lean_apply_2(v_toPure_3992_, lean_box(0), v___x_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3996_, lean_object* v_toBind_3997_, lean_object* v_mkInfo_3998_, lean_object* v_trees_3999_){
_start:
{
lean_object* v___f_4000_; lean_object* v___x_4001_; 
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4000_, 0, v_trees_3999_);
lean_closure_set(v___f_4000_, 1, v_toPure_3996_);
v___x_4001_ = lean_apply_4(v_toBind_3997_, lean_box(0), lean_box(0), v_mkInfo_3998_, v___f_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_4002_, lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_x_4005_, lean_object* v_mkInfo_4006_){
_start:
{
lean_object* v_toApplicative_4007_; lean_object* v_toBind_4008_; lean_object* v_toPure_4009_; lean_object* v___f_4010_; lean_object* v___x_4011_; 
v_toApplicative_4007_ = lean_ctor_get(v_inst_4002_, 0);
v_toBind_4008_ = lean_ctor_get(v_inst_4002_, 1);
v_toPure_4009_ = lean_ctor_get(v_toApplicative_4007_, 1);
lean_inc(v_toBind_4008_);
lean_inc(v_toPure_4009_);
v___f_4010_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4010_, 0, v_toPure_4009_);
lean_closure_set(v___f_4010_, 1, v_toBind_4008_);
lean_closure_set(v___f_4010_, 2, v_mkInfo_4006_);
v___x_4011_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4002_, v_inst_4003_, v_inst_4004_, v_x_4005_, v___f_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_4012_, lean_object* v_inst_4013_, lean_object* v_inst_4014_, lean_object* v_00_u03b1_4015_, lean_object* v_inst_4016_, lean_object* v_x_4017_, lean_object* v_mkInfo_4018_){
_start:
{
lean_object* v_toApplicative_4019_; lean_object* v_toBind_4020_; lean_object* v_toPure_4021_; lean_object* v___f_4022_; lean_object* v___x_4023_; 
v_toApplicative_4019_ = lean_ctor_get(v_inst_4013_, 0);
v_toBind_4020_ = lean_ctor_get(v_inst_4013_, 1);
v_toPure_4021_ = lean_ctor_get(v_toApplicative_4019_, 1);
lean_inc(v_toBind_4020_);
lean_inc(v_toPure_4021_);
v___f_4022_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4022_, 0, v_toPure_4021_);
lean_closure_set(v___f_4022_, 1, v_toBind_4020_);
lean_closure_set(v___f_4022_, 2, v_mkInfo_4018_);
v___x_4023_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4013_, v_inst_4014_, v_inst_4016_, v_x_4017_, v___f_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_4024_, lean_object* v_trees_4025_, lean_object* v_s_4026_){
_start:
{
uint8_t v_enabled_4027_; lean_object* v_assignment_4028_; lean_object* v_lazyAssignment_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4037_; 
v_enabled_4027_ = lean_ctor_get_uint8(v_s_4026_, sizeof(void*)*3);
v_assignment_4028_ = lean_ctor_get(v_s_4026_, 0);
v_lazyAssignment_4029_ = lean_ctor_get(v_s_4026_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_s_4026_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v_s_4026_, 2);
lean_dec(v_unused_4038_);
v___x_4031_ = v_s_4026_;
v_isShared_4032_ = v_isSharedCheck_4037_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_lazyAssignment_4029_);
lean_inc(v_assignment_4028_);
lean_dec(v_s_4026_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4037_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4033_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_4024_, v_trees_4025_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 2, v___x_4033_);
v___x_4035_ = v___x_4031_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_assignment_4028_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_lazyAssignment_4029_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v___x_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4036_, sizeof(void*)*3, v_enabled_4027_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_4039_, lean_object* v_trees_4040_, lean_object* v_s_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_4039_, v_trees_4040_, v_s_4041_);
lean_dec_ref(v_trees_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_4043_, lean_object* v_modifyInfoState_4044_, lean_object* v_trees_4045_){
_start:
{
lean_object* v___f_4046_; lean_object* v___x_4047_; 
v___f_4046_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4046_, 0, v_treesSaved_4043_);
lean_closure_set(v___f_4046_, 1, v_trees_4045_);
v___x_4047_ = lean_apply_1(v_modifyInfoState_4044_, v___f_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_4048_, lean_object* v_tree_4049_, lean_object* v_____do__lift_4050_){
_start:
{
if (lean_obj_tag(v_____do__lift_4050_) == 0)
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_apply_2(v_toPure_4048_, lean_box(0), v_tree_4049_);
return v___x_4051_;
}
else
{
lean_object* v_val_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_val_4052_ = lean_ctor_get(v_____do__lift_4050_, 0);
lean_inc(v_val_4052_);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v_val_4052_);
lean_ctor_set(v___x_4053_, 1, v_tree_4049_);
v___x_4054_ = lean_apply_2(v_toPure_4048_, lean_box(0), v___x_4053_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_4055_, lean_object* v_tree_4056_, lean_object* v_____do__lift_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_4055_, v_tree_4056_, v_____do__lift_4057_);
lean_dec(v_____do__lift_4057_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4059_, lean_object* v_toPure_4060_, lean_object* v_toBind_4061_, lean_object* v_ctx_x3f_4062_, lean_object* v_tree_4063_){
_start:
{
lean_object* v_tree_4064_; lean_object* v___f_4065_; lean_object* v___x_4066_; 
v_tree_4064_ = l_Lean_Elab_InfoTree_substitute(v_tree_4063_, v_assignment_4059_);
v___f_4065_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4065_, 0, v_toPure_4060_);
lean_closure_set(v___f_4065_, 1, v_tree_4064_);
v___x_4066_ = lean_apply_4(v_toBind_4061_, lean_box(0), lean_box(0), v_ctx_x3f_4062_, v___f_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_4067_, lean_object* v_toPure_4068_, lean_object* v_toBind_4069_, lean_object* v_ctx_x3f_4070_, lean_object* v_tree_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_4067_, v_toPure_4068_, v_toBind_4069_, v_ctx_x3f_4070_, v_tree_4071_);
lean_dec_ref(v_assignment_4067_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4073_, lean_object* v_toBind_4074_, lean_object* v_ctx_x3f_4075_, lean_object* v_inst_4076_, lean_object* v___f_4077_, lean_object* v_st_4078_){
_start:
{
lean_object* v_assignment_4079_; lean_object* v_trees_4080_; lean_object* v___f_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_assignment_4079_ = lean_ctor_get(v_st_4078_, 0);
lean_inc_ref(v_assignment_4079_);
v_trees_4080_ = lean_ctor_get(v_st_4078_, 2);
lean_inc_ref(v_trees_4080_);
lean_dec_ref(v_st_4078_);
lean_inc(v_toBind_4074_);
v___f_4081_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4081_, 0, v_assignment_4079_);
lean_closure_set(v___f_4081_, 1, v_toPure_4073_);
lean_closure_set(v___f_4081_, 2, v_toBind_4074_);
lean_closure_set(v___f_4081_, 3, v_ctx_x3f_4075_);
v___x_4082_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4076_, v___f_4081_, v_trees_4080_);
v___x_4083_ = lean_apply_4(v_toBind_4074_, lean_box(0), lean_box(0), v___x_4082_, v___f_4077_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4084_, lean_object* v_modifyInfoState_4085_, lean_object* v_toBind_4086_, lean_object* v_ctx_x3f_4087_, lean_object* v_inst_4088_, lean_object* v_getInfoState_4089_, lean_object* v_inst_4090_, lean_object* v_x_4091_, lean_object* v___f_4092_, lean_object* v_treesSaved_4093_){
_start:
{
lean_object* v_toFunctor_4094_; lean_object* v_toPure_4095_; lean_object* v_map_4096_; lean_object* v___f_4097_; lean_object* v___f_4098_; lean_object* v___f_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_toFunctor_4094_ = lean_ctor_get(v_toApplicative_4084_, 0);
lean_inc_ref(v_toFunctor_4094_);
v_toPure_4095_ = lean_ctor_get(v_toApplicative_4084_, 1);
lean_inc(v_toPure_4095_);
lean_dec_ref(v_toApplicative_4084_);
v_map_4096_ = lean_ctor_get(v_toFunctor_4094_, 0);
lean_inc(v_map_4096_);
lean_dec_ref(v_toFunctor_4094_);
v___f_4097_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4097_, 0, v_treesSaved_4093_);
lean_closure_set(v___f_4097_, 1, v_modifyInfoState_4085_);
lean_inc(v_toBind_4086_);
v___f_4098_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4098_, 0, v_toPure_4095_);
lean_closure_set(v___f_4098_, 1, v_toBind_4086_);
lean_closure_set(v___f_4098_, 2, v_ctx_x3f_4087_);
lean_closure_set(v___f_4098_, 3, v_inst_4088_);
lean_closure_set(v___f_4098_, 4, v___f_4097_);
v___f_4099_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4099_, 0, v_toBind_4086_);
lean_closure_set(v___f_4099_, 1, v_getInfoState_4089_);
lean_closure_set(v___f_4099_, 2, v___f_4098_);
v___x_4100_ = lean_apply_4(v_inst_4090_, lean_box(0), lean_box(0), v_x_4091_, v___f_4099_);
v___x_4101_ = lean_apply_4(v_map_4096_, lean_box(0), lean_box(0), v___f_4092_, v___x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_inst_4104_, lean_object* v_x_4105_, lean_object* v_ctx_x3f_4106_){
_start:
{
lean_object* v_toApplicative_4107_; lean_object* v_toBind_4108_; lean_object* v_getInfoState_4109_; lean_object* v_modifyInfoState_4110_; lean_object* v___f_4111_; lean_object* v___f_4112_; lean_object* v___f_4113_; lean_object* v___x_4114_; 
v_toApplicative_4107_ = lean_ctor_get(v_inst_4102_, 0);
v_toBind_4108_ = lean_ctor_get(v_inst_4102_, 1);
lean_inc_n(v_toBind_4108_, 3);
v_getInfoState_4109_ = lean_ctor_get(v_inst_4103_, 0);
lean_inc_n(v_getInfoState_4109_, 2);
v_modifyInfoState_4110_ = lean_ctor_get(v_inst_4103_, 1);
v___f_4111_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4105_);
lean_inc_ref(v_inst_4102_);
lean_inc(v_modifyInfoState_4110_);
lean_inc_ref(v_toApplicative_4107_);
v___f_4112_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4112_, 0, v_toApplicative_4107_);
lean_closure_set(v___f_4112_, 1, v_modifyInfoState_4110_);
lean_closure_set(v___f_4112_, 2, v_toBind_4108_);
lean_closure_set(v___f_4112_, 3, v_ctx_x3f_4106_);
lean_closure_set(v___f_4112_, 4, v_inst_4102_);
lean_closure_set(v___f_4112_, 5, v_getInfoState_4109_);
lean_closure_set(v___f_4112_, 6, v_inst_4104_);
lean_closure_set(v___f_4112_, 7, v_x_4105_);
lean_closure_set(v___f_4112_, 8, v___f_4111_);
v___f_4113_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4113_, 0, v_x_4105_);
lean_closure_set(v___f_4113_, 1, v_inst_4102_);
lean_closure_set(v___f_4113_, 2, v_inst_4103_);
lean_closure_set(v___f_4113_, 3, v_toBind_4108_);
lean_closure_set(v___f_4113_, 4, v___f_4112_);
v___x_4114_ = lean_apply_4(v_toBind_4108_, lean_box(0), lean_box(0), v_getInfoState_4109_, v___f_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4115_, lean_object* v_inst_4116_, lean_object* v_inst_4117_, lean_object* v_00_u03b1_4118_, lean_object* v_inst_4119_, lean_object* v_x_4120_, lean_object* v_ctx_x3f_4121_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4116_, v_inst_4117_, v_inst_4119_, v_x_4120_, v_ctx_x3f_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4123_, lean_object* v_____do__lift_4124_){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_____do__lift_4124_);
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_apply_2(v_toPure_4123_, lean_box(0), v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4128_, lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_inst_4133_, lean_object* v_inst_4134_, lean_object* v_inst_4135_, lean_object* v_inst_4136_, lean_object* v_x_4137_){
_start:
{
lean_object* v_toApplicative_4138_; lean_object* v_toBind_4139_; lean_object* v_toPure_4140_; lean_object* v___x_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_toApplicative_4138_ = lean_ctor_get(v_inst_4128_, 0);
v_toBind_4139_ = lean_ctor_get(v_inst_4128_, 1);
v_toPure_4140_ = lean_ctor_get(v_toApplicative_4138_, 1);
lean_inc_ref(v_inst_4128_);
v___x_4141_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4128_, v_inst_4132_, v_inst_4134_, v_inst_4133_, v_inst_4135_, v_inst_4130_, v_inst_4136_);
lean_inc(v_toPure_4140_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4142_, 0, v_toPure_4140_);
lean_inc(v_toBind_4139_);
v___x_4143_ = lean_apply_4(v_toBind_4139_, lean_box(0), lean_box(0), v___x_4141_, v___f_4142_);
v___x_4144_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4128_, v_inst_4129_, v_inst_4131_, v_x_4137_, v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4145_, lean_object* v_inst_4146_, lean_object* v_inst_4147_, lean_object* v_00_u03b1_4148_, lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_inst_4152_, lean_object* v_inst_4153_, lean_object* v_inst_4154_, lean_object* v_inst_4155_, lean_object* v_x_4156_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4146_, v_inst_4147_, v_inst_4149_, v_inst_4150_, v_inst_4151_, v_inst_4152_, v_inst_4153_, v_inst_4154_, v_inst_4155_, v_x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4158_, lean_object* v_____x_4159_){
_start:
{
if (lean_obj_tag(v_____x_4159_) == 1)
{
lean_object* v_val_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4169_; 
v_val_4160_ = lean_ctor_get(v_____x_4159_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_____x_4159_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4162_ = v_____x_4159_;
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_val_4160_);
lean_dec(v_____x_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_val_4160_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4164_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_apply_2(v_toPure_4158_, lean_box(0), v___x_4166_);
return v___x_4167_;
}
}
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_dec(v_____x_4159_);
v___x_4170_ = lean_box(0);
v___x_4171_ = lean_apply_2(v_toPure_4158_, lean_box(0), v___x_4170_);
return v___x_4171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_inst_4174_, lean_object* v_inst_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v_toApplicative_4177_; lean_object* v_toBind_4178_; lean_object* v_toPure_4179_; lean_object* v___f_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_toApplicative_4177_ = lean_ctor_get(v_inst_4172_, 0);
v_toBind_4178_ = lean_ctor_get(v_inst_4172_, 1);
v_toPure_4179_ = lean_ctor_get(v_toApplicative_4177_, 1);
lean_inc(v_toPure_4179_);
v___f_4180_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4180_, 0, v_toPure_4179_);
lean_inc(v_toBind_4178_);
v___x_4181_ = lean_apply_4(v_toBind_4178_, lean_box(0), lean_box(0), v_inst_4175_, v___f_4180_);
v___x_4182_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4172_, v_inst_4173_, v_inst_4174_, v_x_4176_, v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4183_, lean_object* v_inst_4184_, lean_object* v_inst_4185_, lean_object* v_00_u03b1_4186_, lean_object* v_inst_4187_, lean_object* v_inst_4188_, lean_object* v_x_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4184_, v_inst_4185_, v_inst_4187_, v_inst_4188_, v_x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4191_, lean_object* v_autoImplicits_4192_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_autoImplicits_4192_);
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
v___x_4195_ = lean_apply_2(v_toPure_4191_, lean_box(0), v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_x_4200_){
_start:
{
lean_object* v_toApplicative_4201_; lean_object* v_toBind_4202_; lean_object* v_toPure_4203_; lean_object* v___f_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_toApplicative_4201_ = lean_ctor_get(v_inst_4196_, 0);
v_toBind_4202_ = lean_ctor_get(v_inst_4196_, 1);
v_toPure_4203_ = lean_ctor_get(v_toApplicative_4201_, 1);
lean_inc(v_toPure_4203_);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4204_, 0, v_toPure_4203_);
lean_inc(v_toBind_4202_);
v___x_4205_ = lean_apply_4(v_toBind_4202_, lean_box(0), lean_box(0), v_inst_4199_, v___f_4204_);
v___x_4206_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4196_, v_inst_4197_, v_inst_4198_, v_x_4200_, v___x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4207_, lean_object* v_inst_4208_, lean_object* v_inst_4209_, lean_object* v_00_u03b1_4210_, lean_object* v_inst_4211_, lean_object* v_inst_4212_, lean_object* v_x_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4208_, v_inst_4209_, v_inst_4211_, v_inst_4212_, v_x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v_mvarId_4217_, lean_object* v_toPure_4218_, lean_object* v_____do__lift_4219_){
_start:
{
lean_object* v_assignment_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_assignment_4220_ = lean_ctor_get(v_____do__lift_4219_, 0);
v___x_4221_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4215_, v___x_4216_, v_assignment_4220_, v_mvarId_4217_);
v___x_4222_ = lean_apply_2(v_toPure_4218_, lean_box(0), v___x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v_mvarId_4225_, lean_object* v_toPure_4226_, lean_object* v_____do__lift_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_4223_, v___x_4224_, v_mvarId_4225_, v_toPure_4226_, v_____do__lift_4227_);
lean_dec_ref(v_____do__lift_4227_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4231_, lean_object* v_inst_4232_, lean_object* v_mvarId_4233_){
_start:
{
lean_object* v_toApplicative_4234_; lean_object* v_toBind_4235_; lean_object* v_getInfoState_4236_; lean_object* v_toPure_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v___x_4241_; 
v_toApplicative_4234_ = lean_ctor_get(v_inst_4231_, 0);
lean_inc_ref(v_toApplicative_4234_);
v_toBind_4235_ = lean_ctor_get(v_inst_4231_, 1);
lean_inc(v_toBind_4235_);
lean_dec_ref(v_inst_4231_);
v_getInfoState_4236_ = lean_ctor_get(v_inst_4232_, 0);
lean_inc(v_getInfoState_4236_);
lean_dec_ref(v_inst_4232_);
v_toPure_4237_ = lean_ctor_get(v_toApplicative_4234_, 1);
lean_inc(v_toPure_4237_);
lean_dec_ref(v_toApplicative_4234_);
v___x_4238_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4239_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4240_, 0, v___x_4238_);
lean_closure_set(v___f_4240_, 1, v___x_4239_);
lean_closure_set(v___f_4240_, 2, v_mvarId_4233_);
lean_closure_set(v___f_4240_, 3, v_toPure_4237_);
v___x_4241_ = lean_apply_4(v_toBind_4235_, lean_box(0), lean_box(0), v_getInfoState_4236_, v___f_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4242_, lean_object* v_inst_4243_, lean_object* v_inst_4244_, lean_object* v_mvarId_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4243_, v_inst_4244_, v_mvarId_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4247_, lean_object* v_infoTree_4248_, lean_object* v_s_4249_){
_start:
{
uint8_t v_enabled_4250_; lean_object* v_assignment_4251_; lean_object* v_lazyAssignment_4252_; lean_object* v_trees_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4263_; 
v_enabled_4250_ = lean_ctor_get_uint8(v_s_4249_, sizeof(void*)*3);
v_assignment_4251_ = lean_ctor_get(v_s_4249_, 0);
v_lazyAssignment_4252_ = lean_ctor_get(v_s_4249_, 1);
v_trees_4253_ = lean_ctor_get(v_s_4249_, 2);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_s_4249_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4255_ = v_s_4249_;
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_trees_4253_);
lean_inc(v_lazyAssignment_4252_);
lean_inc(v_assignment_4251_);
lean_dec(v_s_4249_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4257_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4258_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4259_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4257_, v___x_4258_, v_assignment_4251_, v_mvarId_4247_, v_infoTree_4248_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4259_);
v___x_4261_ = v___x_4255_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_lazyAssignment_4252_);
lean_ctor_set(v_reuseFailAlloc_4262_, 2, v_trees_4253_);
lean_ctor_set_uint8(v_reuseFailAlloc_4262_, sizeof(void*)*3, v_enabled_4250_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4266_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4267_ = lean_unsigned_to_nat(2u);
v___x_4268_ = lean_unsigned_to_nat(491u);
v___x_4269_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4270_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4271_ = l_mkPanicMessageWithDecl(v___x_4270_, v___x_4269_, v___x_4268_, v___x_4267_, v___x_4266_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4272_, lean_object* v___f_4273_, lean_object* v_inst_4274_, lean_object* v_____do__lift_4275_){
_start:
{
if (lean_obj_tag(v_____do__lift_4275_) == 0)
{
lean_object* v_modifyInfoState_4276_; lean_object* v___x_4277_; 
lean_dec_ref(v_inst_4274_);
v_modifyInfoState_4276_ = lean_ctor_get(v_inst_4272_, 1);
lean_inc(v_modifyInfoState_4276_);
lean_dec_ref(v_inst_4272_);
v___x_4277_ = lean_apply_1(v_modifyInfoState_4276_, v___f_4273_);
return v___x_4277_;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_dec_ref(v___f_4273_);
lean_dec_ref(v_inst_4272_);
v___x_4278_ = lean_box(0);
v___x_4279_ = l_instInhabitedOfMonad___redArg(v_inst_4274_, v___x_4278_);
v___x_4280_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4281_ = l_panic___redArg(v___x_4279_, v___x_4280_);
lean_dec(v___x_4279_);
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4282_, lean_object* v___f_4283_, lean_object* v_inst_4284_, lean_object* v_____do__lift_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4282_, v___f_4283_, v_inst_4284_, v_____do__lift_4285_);
lean_dec(v_____do__lift_4285_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4287_, lean_object* v_inst_4288_, lean_object* v_mvarId_4289_, lean_object* v_infoTree_4290_){
_start:
{
lean_object* v_toBind_4291_; lean_object* v___f_4292_; lean_object* v___f_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_toBind_4291_ = lean_ctor_get(v_inst_4287_, 1);
lean_inc(v_toBind_4291_);
lean_inc(v_mvarId_4289_);
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4292_, 0, v_mvarId_4289_);
lean_closure_set(v___f_4292_, 1, v_infoTree_4290_);
lean_inc_ref(v_inst_4287_);
lean_inc_ref(v_inst_4288_);
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4293_, 0, v_inst_4288_);
lean_closure_set(v___f_4293_, 1, v___f_4292_);
lean_closure_set(v___f_4293_, 2, v_inst_4287_);
v___x_4294_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4287_, v_inst_4288_, v_mvarId_4289_);
v___x_4295_ = lean_apply_4(v_toBind_4291_, lean_box(0), lean_box(0), v___x_4294_, v___f_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4296_, lean_object* v_inst_4297_, lean_object* v_inst_4298_, lean_object* v_mvarId_4299_, lean_object* v_infoTree_4300_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4297_, v_inst_4298_, v_mvarId_4299_, v_infoTree_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4302_, lean_object* v_output_4303_, lean_object* v_toPure_4304_, lean_object* v_____do__lift_4305_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4306_, 0, v_____do__lift_4305_);
lean_ctor_set(v___x_4306_, 1, v_stx_4302_);
lean_ctor_set(v___x_4306_, 2, v_output_4303_);
v___x_4307_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
v___x_4308_ = lean_apply_2(v_toPure_4304_, lean_box(0), v___x_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4309_, lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_stx_4313_, lean_object* v_output_4314_, lean_object* v_x_4315_){
_start:
{
lean_object* v_toApplicative_4316_; lean_object* v_toBind_4317_; lean_object* v_toPure_4318_; lean_object* v___f_4319_; lean_object* v_mkInfo_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; 
v_toApplicative_4316_ = lean_ctor_get(v_inst_4310_, 0);
v_toBind_4317_ = lean_ctor_get(v_inst_4310_, 1);
v_toPure_4318_ = lean_ctor_get(v_toApplicative_4316_, 1);
lean_inc_n(v_toPure_4318_, 2);
v___f_4319_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4319_, 0, v_stx_4313_);
lean_closure_set(v___f_4319_, 1, v_output_4314_);
lean_closure_set(v___f_4319_, 2, v_toPure_4318_);
lean_inc_n(v_toBind_4317_, 2);
v_mkInfo_4320_ = lean_apply_4(v_toBind_4317_, lean_box(0), lean_box(0), v_inst_4312_, v___f_4319_);
v___f_4321_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4321_, 0, v_toPure_4318_);
lean_closure_set(v___f_4321_, 1, v_toBind_4317_);
lean_closure_set(v___f_4321_, 2, v_mkInfo_4320_);
v___x_4322_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4310_, v_inst_4311_, v_inst_4309_, v_x_4315_, v___f_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4323_, lean_object* v_00_u03b1_4324_, lean_object* v_inst_4325_, lean_object* v_inst_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_, lean_object* v_stx_4329_, lean_object* v_output_4330_, lean_object* v_x_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4325_, v_inst_4326_, v_inst_4327_, v_inst_4328_, v_stx_4329_, v_output_4330_, v_x_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4333_, lean_object* v_mvarId_4334_, lean_object* v_s_4335_){
_start:
{
lean_object* v_trees_4336_; uint8_t v_enabled_4337_; lean_object* v_assignment_4338_; lean_object* v_lazyAssignment_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4359_; 
v_trees_4336_ = lean_ctor_get(v_s_4335_, 2);
v_enabled_4337_ = lean_ctor_get_uint8(v_s_4335_, sizeof(void*)*3);
v_assignment_4338_ = lean_ctor_get(v_s_4335_, 0);
v_lazyAssignment_4339_ = lean_ctor_get(v_s_4335_, 1);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_s_4335_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4341_ = v_s_4335_;
v_isShared_4342_ = v_isSharedCheck_4359_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_trees_4336_);
lean_inc(v_lazyAssignment_4339_);
lean_inc(v_assignment_4338_);
lean_dec(v_s_4335_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4359_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v_size_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_size_4343_ = lean_ctor_get(v_trees_4336_, 2);
v___x_4344_ = lean_unsigned_to_nat(0u);
v___x_4345_ = lean_nat_dec_lt(v___x_4344_, v_size_4343_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4347_; 
lean_dec_ref(v_trees_4336_);
lean_dec(v_mvarId_4334_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 2, v_treesSaved_4333_);
v___x_4347_ = v___x_4341_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_assignment_4338_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_lazyAssignment_4339_);
lean_ctor_set(v_reuseFailAlloc_4348_, 2, v_treesSaved_4333_);
lean_ctor_set_uint8(v_reuseFailAlloc_4348_, sizeof(void*)*3, v_enabled_4337_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
else
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4350_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4351_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4352_ = lean_unsigned_to_nat(1u);
v___x_4353_ = lean_nat_sub(v_size_4343_, v___x_4352_);
v___x_4354_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4351_, v_trees_4336_, v___x_4353_);
lean_dec(v___x_4353_);
lean_dec_ref(v_trees_4336_);
v___x_4355_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4349_, v___x_4350_, v_assignment_4338_, v_mvarId_4334_, v___x_4354_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 2, v_treesSaved_4333_);
lean_ctor_set(v___x_4341_, 0, v___x_4355_);
v___x_4357_ = v___x_4341_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_lazyAssignment_4339_);
lean_ctor_set(v_reuseFailAlloc_4358_, 2, v_treesSaved_4333_);
lean_ctor_set_uint8(v_reuseFailAlloc_4358_, sizeof(void*)*3, v_enabled_4337_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4360_, lean_object* v___f_4361_, lean_object* v_x_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = lean_apply_1(v_modifyInfoState_4360_, v___f_4361_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4364_, lean_object* v___f_4365_, lean_object* v_x_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4364_, v___f_4365_, v_x_4366_);
lean_dec(v_x_4366_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4368_, lean_object* v_mvarId_4369_, lean_object* v_modifyInfoState_4370_, lean_object* v_inst_4371_, lean_object* v_x_4372_, lean_object* v___f_4373_, lean_object* v_treesSaved_4374_){
_start:
{
lean_object* v_toFunctor_4375_; lean_object* v_map_4376_; lean_object* v___f_4377_; lean_object* v___f_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_toFunctor_4375_ = lean_ctor_get(v_toApplicative_4368_, 0);
lean_inc_ref(v_toFunctor_4375_);
lean_dec_ref(v_toApplicative_4368_);
v_map_4376_ = lean_ctor_get(v_toFunctor_4375_, 0);
lean_inc(v_map_4376_);
lean_dec_ref(v_toFunctor_4375_);
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4377_, 0, v_treesSaved_4374_);
lean_closure_set(v___f_4377_, 1, v_mvarId_4369_);
v___f_4378_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4378_, 0, v_modifyInfoState_4370_);
lean_closure_set(v___f_4378_, 1, v___f_4377_);
v___x_4379_ = lean_apply_4(v_inst_4371_, lean_box(0), lean_box(0), v_x_4372_, v___f_4378_);
v___x_4380_ = lean_apply_4(v_map_4376_, lean_box(0), lean_box(0), v___f_4373_, v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4381_, lean_object* v_inst_4382_, lean_object* v_inst_4383_, lean_object* v_mvarId_4384_, lean_object* v_x_4385_){
_start:
{
lean_object* v_toApplicative_4386_; lean_object* v_toBind_4387_; lean_object* v_getInfoState_4388_; lean_object* v_modifyInfoState_4389_; lean_object* v___f_4390_; lean_object* v___f_4391_; lean_object* v___f_4392_; lean_object* v___x_4393_; 
v_toApplicative_4386_ = lean_ctor_get(v_inst_4382_, 0);
v_toBind_4387_ = lean_ctor_get(v_inst_4382_, 1);
lean_inc_n(v_toBind_4387_, 2);
v_getInfoState_4388_ = lean_ctor_get(v_inst_4383_, 0);
lean_inc(v_getInfoState_4388_);
v_modifyInfoState_4389_ = lean_ctor_get(v_inst_4383_, 1);
v___f_4390_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4385_);
lean_inc(v_modifyInfoState_4389_);
lean_inc_ref(v_toApplicative_4386_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4391_, 0, v_toApplicative_4386_);
lean_closure_set(v___f_4391_, 1, v_mvarId_4384_);
lean_closure_set(v___f_4391_, 2, v_modifyInfoState_4389_);
lean_closure_set(v___f_4391_, 3, v_inst_4381_);
lean_closure_set(v___f_4391_, 4, v_x_4385_);
lean_closure_set(v___f_4391_, 5, v___f_4390_);
v___f_4392_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4392_, 0, v_x_4385_);
lean_closure_set(v___f_4392_, 1, v_inst_4382_);
lean_closure_set(v___f_4392_, 2, v_inst_4383_);
lean_closure_set(v___f_4392_, 3, v_toBind_4387_);
lean_closure_set(v___f_4392_, 4, v___f_4391_);
v___x_4393_ = lean_apply_4(v_toBind_4387_, lean_box(0), lean_box(0), v_getInfoState_4388_, v___f_4392_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4394_, lean_object* v_00_u03b1_4395_, lean_object* v_inst_4396_, lean_object* v_inst_4397_, lean_object* v_inst_4398_, lean_object* v_mvarId_4399_, lean_object* v_x_4400_){
_start:
{
lean_object* v_toApplicative_4401_; lean_object* v_toBind_4402_; lean_object* v_getInfoState_4403_; lean_object* v_modifyInfoState_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; 
v_toApplicative_4401_ = lean_ctor_get(v_inst_4397_, 0);
v_toBind_4402_ = lean_ctor_get(v_inst_4397_, 1);
lean_inc_n(v_toBind_4402_, 2);
v_getInfoState_4403_ = lean_ctor_get(v_inst_4398_, 0);
lean_inc(v_getInfoState_4403_);
v_modifyInfoState_4404_ = lean_ctor_get(v_inst_4398_, 1);
v___f_4405_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4400_);
lean_inc(v_modifyInfoState_4404_);
lean_inc_ref(v_toApplicative_4401_);
v___f_4406_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4406_, 0, v_toApplicative_4401_);
lean_closure_set(v___f_4406_, 1, v_mvarId_4399_);
lean_closure_set(v___f_4406_, 2, v_modifyInfoState_4404_);
lean_closure_set(v___f_4406_, 3, v_inst_4396_);
lean_closure_set(v___f_4406_, 4, v_x_4400_);
lean_closure_set(v___f_4406_, 5, v___f_4405_);
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4407_, 0, v_x_4400_);
lean_closure_set(v___f_4407_, 1, v_inst_4397_);
lean_closure_set(v___f_4407_, 2, v_inst_4398_);
lean_closure_set(v___f_4407_, 3, v_toBind_4402_);
lean_closure_set(v___f_4407_, 4, v___f_4406_);
v___x_4408_ = lean_apply_4(v_toBind_4402_, lean_box(0), lean_box(0), v_getInfoState_4403_, v___f_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4409_, lean_object* v_s_4410_){
_start:
{
lean_object* v_assignment_4411_; lean_object* v_lazyAssignment_4412_; lean_object* v_trees_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
v_assignment_4411_ = lean_ctor_get(v_s_4410_, 0);
v_lazyAssignment_4412_ = lean_ctor_get(v_s_4410_, 1);
v_trees_4413_ = lean_ctor_get(v_s_4410_, 2);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_s_4410_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v_s_4410_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_trees_4413_);
lean_inc(v_lazyAssignment_4412_);
lean_inc(v_assignment_4411_);
lean_dec(v_s_4410_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_assignment_4411_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_lazyAssignment_4412_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_trees_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_ctor_set_uint8(v___x_4418_, sizeof(void*)*3, v_flag_4409_);
return v___x_4418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4421_, lean_object* v_s_4422_){
_start:
{
uint8_t v_flag_boxed_4423_; lean_object* v_res_4424_; 
v_flag_boxed_4423_ = lean_unbox(v_flag_4421_);
v_res_4424_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4423_, v_s_4422_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4425_, uint8_t v_flag_4426_){
_start:
{
lean_object* v_modifyInfoState_4427_; lean_object* v___x_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; 
v_modifyInfoState_4427_ = lean_ctor_get(v_inst_4425_, 1);
lean_inc(v_modifyInfoState_4427_);
lean_dec_ref(v_inst_4425_);
v___x_4428_ = lean_box(v_flag_4426_);
v___f_4429_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4429_, 0, v___x_4428_);
v___x_4430_ = lean_apply_1(v_modifyInfoState_4427_, v___f_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4431_, lean_object* v_flag_4432_){
_start:
{
uint8_t v_flag_boxed_4433_; lean_object* v_res_4434_; 
v_flag_boxed_4433_ = lean_unbox(v_flag_4432_);
v_res_4434_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4431_, v_flag_boxed_4433_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4435_, lean_object* v_inst_4436_, uint8_t v_flag_4437_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4436_, v_flag_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4439_, lean_object* v_inst_4440_, lean_object* v_flag_4441_){
_start:
{
uint8_t v_flag_boxed_4442_; lean_object* v_res_4443_; 
v_flag_boxed_4442_ = lean_unbox(v_flag_4441_);
v_res_4443_ = l_Lean_Elab_enableInfoTree(v_m_4439_, v_inst_4440_, v_flag_boxed_4442_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4444_){
_start:
{
lean_object* v_fst_4445_; 
v_fst_4445_ = lean_ctor_get(v_x_4444_, 0);
lean_inc(v_fst_4445_);
return v_fst_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4446_);
lean_dec_ref(v_x_4446_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4448_, lean_object* v_____r_4449_){
_start:
{
lean_inc(v_x_4448_);
return v_x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4450_, lean_object* v_____r_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4450_, v_____r_4451_);
lean_dec(v_x_4450_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4453_, lean_object* v_x_4454_){
_start:
{
lean_inc(v___x_4453_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4455_, lean_object* v_x_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4455_, v_x_4456_);
lean_dec(v_x_4456_);
lean_dec(v___x_4455_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4458_, lean_object* v_inst_4459_, uint8_t v_flag_4460_, lean_object* v_toBind_4461_, lean_object* v___f_4462_, lean_object* v_inst_4463_, lean_object* v___f_4464_, lean_object* v_____do__lift_4465_){
_start:
{
uint8_t v_enabled_4466_; lean_object* v_map_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___f_4471_; lean_object* v_y_4472_; lean_object* v___x_4473_; 
v_enabled_4466_ = lean_ctor_get_uint8(v_____do__lift_4465_, sizeof(void*)*3);
v_map_4467_ = lean_ctor_get(v_toFunctor_4458_, 0);
lean_inc(v_map_4467_);
lean_dec_ref(v_toFunctor_4458_);
lean_inc_ref(v_inst_4459_);
v___x_4468_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4459_, v_flag_4460_);
v___x_4469_ = lean_apply_4(v_toBind_4461_, lean_box(0), lean_box(0), v___x_4468_, v___f_4462_);
v___x_4470_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4459_, v_enabled_4466_);
v___f_4471_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4471_, 0, v___x_4470_);
v_y_4472_ = lean_apply_4(v_inst_4463_, lean_box(0), lean_box(0), v___x_4469_, v___f_4471_);
v___x_4473_ = lean_apply_4(v_map_4467_, lean_box(0), lean_box(0), v___f_4464_, v_y_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4474_, lean_object* v_inst_4475_, lean_object* v_flag_4476_, lean_object* v_toBind_4477_, lean_object* v___f_4478_, lean_object* v_inst_4479_, lean_object* v___f_4480_, lean_object* v_____do__lift_4481_){
_start:
{
uint8_t v_flag_boxed_4482_; lean_object* v_res_4483_; 
v_flag_boxed_4482_ = lean_unbox(v_flag_4476_);
v_res_4483_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4474_, v_inst_4475_, v_flag_boxed_4482_, v_toBind_4477_, v___f_4478_, v_inst_4479_, v___f_4480_, v_____do__lift_4481_);
lean_dec_ref(v_____do__lift_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4485_, lean_object* v_inst_4486_, lean_object* v_inst_4487_, uint8_t v_flag_4488_, lean_object* v_x_4489_){
_start:
{
lean_object* v_toApplicative_4490_; lean_object* v_toBind_4491_; lean_object* v_getInfoState_4492_; lean_object* v_toFunctor_4493_; lean_object* v___f_4494_; lean_object* v___f_4495_; lean_object* v___x_4496_; lean_object* v___f_4497_; lean_object* v___x_4498_; 
v_toApplicative_4490_ = lean_ctor_get(v_inst_4485_, 0);
lean_inc_ref(v_toApplicative_4490_);
v_toBind_4491_ = lean_ctor_get(v_inst_4485_, 1);
lean_inc_n(v_toBind_4491_, 2);
lean_dec_ref(v_inst_4485_);
v_getInfoState_4492_ = lean_ctor_get(v_inst_4486_, 0);
lean_inc(v_getInfoState_4492_);
v_toFunctor_4493_ = lean_ctor_get(v_toApplicative_4490_, 0);
lean_inc_ref(v_toFunctor_4493_);
lean_dec_ref(v_toApplicative_4490_);
v___f_4494_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4495_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4495_, 0, v_x_4489_);
v___x_4496_ = lean_box(v_flag_4488_);
v___f_4497_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4497_, 0, v_toFunctor_4493_);
lean_closure_set(v___f_4497_, 1, v_inst_4486_);
lean_closure_set(v___f_4497_, 2, v___x_4496_);
lean_closure_set(v___f_4497_, 3, v_toBind_4491_);
lean_closure_set(v___f_4497_, 4, v___f_4495_);
lean_closure_set(v___f_4497_, 5, v_inst_4487_);
lean_closure_set(v___f_4497_, 6, v___f_4494_);
v___x_4498_ = lean_apply_4(v_toBind_4491_, lean_box(0), lean_box(0), v_getInfoState_4492_, v___f_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4499_, lean_object* v_inst_4500_, lean_object* v_inst_4501_, lean_object* v_flag_4502_, lean_object* v_x_4503_){
_start:
{
uint8_t v_flag_boxed_4504_; lean_object* v_res_4505_; 
v_flag_boxed_4504_ = lean_unbox(v_flag_4502_);
v_res_4505_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4499_, v_inst_4500_, v_inst_4501_, v_flag_boxed_4504_, v_x_4503_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4506_, lean_object* v_00_u03b1_4507_, lean_object* v_inst_4508_, lean_object* v_inst_4509_, lean_object* v_inst_4510_, uint8_t v_flag_4511_, lean_object* v_x_4512_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4508_, v_inst_4509_, v_inst_4510_, v_flag_4511_, v_x_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4514_, lean_object* v_00_u03b1_4515_, lean_object* v_inst_4516_, lean_object* v_inst_4517_, lean_object* v_inst_4518_, lean_object* v_flag_4519_, lean_object* v_x_4520_){
_start:
{
uint8_t v_flag_boxed_4521_; lean_object* v_res_4522_; 
v_flag_boxed_4521_ = lean_unbox(v_flag_4519_);
v_res_4522_ = l_Lean_Elab_withEnableInfoTree(v_m_4514_, v_00_u03b1_4515_, v_inst_4516_, v_inst_4517_, v_inst_4518_, v_flag_boxed_4521_, v_x_4520_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4523_, lean_object* v_____do__lift_4524_){
_start:
{
lean_object* v_trees_4525_; lean_object* v___x_4526_; 
v_trees_4525_ = lean_ctor_get(v_____do__lift_4524_, 2);
lean_inc_ref(v_trees_4525_);
lean_dec_ref(v_____do__lift_4524_);
v___x_4526_ = lean_apply_2(v_toPure_4523_, lean_box(0), v_trees_4525_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4527_, lean_object* v_inst_4528_){
_start:
{
lean_object* v_toApplicative_4529_; lean_object* v_toBind_4530_; lean_object* v_getInfoState_4531_; lean_object* v_toPure_4532_; lean_object* v___f_4533_; lean_object* v___x_4534_; 
v_toApplicative_4529_ = lean_ctor_get(v_inst_4528_, 0);
lean_inc_ref(v_toApplicative_4529_);
v_toBind_4530_ = lean_ctor_get(v_inst_4528_, 1);
lean_inc(v_toBind_4530_);
lean_dec_ref(v_inst_4528_);
v_getInfoState_4531_ = lean_ctor_get(v_inst_4527_, 0);
lean_inc(v_getInfoState_4531_);
lean_dec_ref(v_inst_4527_);
v_toPure_4532_ = lean_ctor_get(v_toApplicative_4529_, 1);
lean_inc(v_toPure_4532_);
lean_dec_ref(v_toApplicative_4529_);
v___f_4533_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4533_, 0, v_toPure_4532_);
v___x_4534_ = lean_apply_4(v_toBind_4530_, lean_box(0), lean_box(0), v_getInfoState_4531_, v___f_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4535_, lean_object* v_inst_4536_, lean_object* v_inst_4537_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4536_, v_inst_4537_);
return v___x_4538_;
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
