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
static const lean_string_object l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2_value;
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2278_;
}
else
{
lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2290_; 
v_val_2279_ = lean_ctor_get(v_x_2276_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2281_ = v_x_2276_;
v_isShared_2282_ = v_isSharedCheck_2290_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_val_2279_);
lean_dec(v_x_2276_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2290_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2284_ = l_String_quote(v_val_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set_tag(v___x_2281_, 3);
lean_ctor_set(v___x_2281_, 0, v___x_2284_);
v___x_2286_ = v___x_2281_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2283_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Repr_addAppParen(v___x_2287_, v_x_2277_);
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2291_, v_x_2292_);
lean_dec(v_x_2292_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2308_, lean_object* v_info_2309_){
_start:
{
lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v_toTermInfo_2317_; lean_object* v_location_x3f_2318_; lean_object* v_docString_x3f_2319_; uint8_t v_explicit_2320_; lean_object* v___y_2322_; 
v_toTermInfo_2317_ = lean_ctor_get(v_info_2309_, 0);
lean_inc_ref(v_toTermInfo_2317_);
v_location_x3f_2318_ = lean_ctor_get(v_info_2309_, 1);
lean_inc(v_location_x3f_2318_);
v_docString_x3f_2319_ = lean_ctor_get(v_info_2309_, 2);
lean_inc(v_docString_x3f_2319_);
v_explicit_2320_ = lean_ctor_get_uint8(v_info_2309_, sizeof(void*)*3);
lean_dec_ref(v_info_2309_);
if (lean_obj_tag(v_location_x3f_2318_) == 1)
{
lean_object* v_val_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2400_; 
v_val_2339_ = lean_ctor_get(v_location_x3f_2318_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_location_x3f_2318_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2341_ = v_location_x3f_2318_;
v_isShared_2342_ = v_isSharedCheck_2400_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_val_2339_);
lean_dec(v_location_x3f_2318_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2400_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_range_2343_; lean_object* v_pos_2344_; lean_object* v_endPos_2345_; lean_object* v_module_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2398_; 
v_range_2343_ = lean_ctor_get(v_val_2339_, 1);
v_pos_2344_ = lean_ctor_get(v_range_2343_, 0);
lean_inc_ref(v_pos_2344_);
v_endPos_2345_ = lean_ctor_get(v_range_2343_, 2);
lean_inc_ref(v_endPos_2345_);
v_module_2346_ = lean_ctor_get(v_val_2339_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_val_2339_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_val_2339_, 1);
lean_dec(v_unused_2399_);
v___x_2348_ = v_val_2339_;
v_isShared_2349_ = v_isSharedCheck_2398_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_module_2346_);
lean_dec(v_val_2339_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2398_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_line_2350_; lean_object* v_column_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2397_; 
v_line_2350_ = lean_ctor_get(v_pos_2344_, 0);
v_column_2351_ = lean_ctor_get(v_pos_2344_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_pos_2344_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2353_ = v_pos_2344_;
v_isShared_2354_ = v_isSharedCheck_2397_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_column_2351_);
lean_inc(v_line_2350_);
lean_dec(v_pos_2344_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2397_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_line_2355_; lean_object* v_column_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2396_; 
v_line_2355_ = lean_ctor_get(v_endPos_2345_, 0);
v_column_2356_ = lean_ctor_get(v_endPos_2345_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_endPos_2345_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2358_ = v_endPos_2345_;
v_isShared_2359_ = v_isSharedCheck_2396_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_column_2356_);
lean_inc(v_line_2355_);
lean_dec(v_endPos_2345_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2396_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2360_ = 1;
v___x_2361_ = l_Lean_Name_toString(v_module_2346_, v___x_2360_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 3);
lean_ctor_set(v___x_2341_, 0, v___x_2361_);
v___x_2363_ = v___x_2341_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 5);
lean_ctor_set(v___x_2358_, 1, v___x_2364_);
lean_ctor_set(v___x_2358_, 0, v___x_2363_);
v___x_2366_ = v___x_2358_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2368_ = l_Nat_reprFast(v_line_2350_);
v___x_2369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 5);
lean_ctor_set(v___x_2353_, 1, v___x_2369_);
lean_ctor_set(v___x_2353_, 0, v___x_2367_);
v___x_2371_ = v___x_2353_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 5);
lean_ctor_set(v___x_2348_, 1, v___x_2372_);
lean_ctor_set(v___x_2348_, 0, v___x_2371_);
v___x_2374_ = v___x_2348_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2375_ = l_Nat_reprFast(v_column_2351_);
v___x_2376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2374_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2366_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l_Nat_reprFast(v_line_2355_);
v___x_2384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2367_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2372_);
v___x_2387_ = l_Nat_reprFast(v_column_2356_);
v___x_2388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2378_);
v___x_2391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2382_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___y_2322_ = v___x_2391_;
goto v___jp_2321_;
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
lean_object* v___x_2401_; 
lean_dec(v_location_x3f_2318_);
v___x_2401_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2322_ = v___x_2401_;
goto v___jp_2321_;
}
v___jp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc_ref(v___y_2313_);
v___x_2314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___y_2313_);
v___x_2315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___y_2312_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
v___jp_2321_:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Elab_TermInfo_format(v_ctx_2308_, v_toTermInfo_2317_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2324_);
v___x_2327_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___y_2322_);
v___x_2330_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_docString_x3f_2319_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
if (v_explicit_2320_ == 0)
{
lean_object* v___x_2337_; 
v___x_2337_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2312_ = v___x_2336_;
v___y_2313_ = v___x_2337_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2312_ = v___x_2336_;
v___y_2313_ = v___x_2338_;
goto v___jp_2311_;
}
}
else
{
lean_dec(v___y_2322_);
lean_dec(v_docString_x3f_2319_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2402_, lean_object* v_info_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2402_, v_info_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2409_, lean_object* v_info_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2412_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2409_, v_info_2410_);
v___x_2413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2417_, lean_object* v_info_2418_){
_start:
{
lean_object* v_stx_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_stx_2419_ = lean_ctor_get(v_info_2418_, 1);
v___x_2420_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2419_);
v___x_2421_ = l_Lean_Syntax_getKind(v_stx_2419_);
v___x_2422_ = 1;
v___x_2423_ = l_Lean_Name_toString(v___x_2421_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2420_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2417_, v_info_2418_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2439_, lean_object* v_info_2440_){
_start:
{
lean_object* v_toElabInfo_2441_; lean_object* v_name_2442_; uint8_t v_kind_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_toElabInfo_2441_ = lean_ctor_get(v_info_2440_, 0);
lean_inc_ref(v_toElabInfo_2441_);
v_name_2442_ = lean_ctor_get(v_info_2440_, 1);
lean_inc(v_name_2442_);
v_kind_2443_ = lean_ctor_get_uint8(v_info_2440_, sizeof(void*)*2);
lean_dec_ref(v_info_2440_);
v___x_2444_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2445_ = 1;
v___x_2446_ = l_Lean_Name_toString(v_name_2442_, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2444_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2443_, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2450_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2439_, v_toElabInfo_2441_);
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2458_, lean_object* v_x_2459_){
_start:
{
switch(lean_obj_tag(v_x_2459_))
{
case 0:
{
lean_object* v_i_2461_; lean_object* v___x_2462_; 
v_i_2461_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2461_);
lean_dec_ref(v_x_2459_);
v___x_2462_ = l_Lean_Elab_TacticInfo_format(v_ctx_2458_, v_i_2461_);
return v___x_2462_;
}
case 1:
{
lean_object* v_i_2463_; lean_object* v___x_2464_; 
v_i_2463_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2463_);
lean_dec_ref(v_x_2459_);
v___x_2464_ = l_Lean_Elab_TermInfo_format(v_ctx_2458_, v_i_2463_);
return v___x_2464_;
}
case 2:
{
lean_object* v_i_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
v_i_2465_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2467_ = v_x_2459_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_i_2465_);
lean_dec(v_x_2459_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2458_, v_i_2465_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
case 3:
{
lean_object* v_i_2474_; lean_object* v___x_2475_; 
v_i_2474_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2474_);
lean_dec_ref(v_x_2459_);
v___x_2475_ = l_Lean_Elab_CommandInfo_format(v_ctx_2458_, v_i_2474_);
return v___x_2475_;
}
case 4:
{
lean_object* v_i_2476_; lean_object* v___x_2477_; 
v_i_2476_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2476_);
lean_dec_ref(v_x_2459_);
v___x_2477_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2458_, v_i_2476_);
lean_dec_ref(v_ctx_2458_);
return v___x_2477_;
}
case 5:
{
lean_object* v_i_2478_; lean_object* v___x_2479_; 
v_i_2478_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2478_);
lean_dec_ref(v_x_2459_);
v___x_2479_ = l_Lean_Elab_OptionInfo_format(v_ctx_2458_, v_i_2478_);
return v___x_2479_;
}
case 6:
{
lean_object* v_i_2480_; lean_object* v___x_2481_; 
v_i_2480_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2480_);
lean_dec_ref(v_x_2459_);
v___x_2481_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2458_, v_i_2480_);
return v___x_2481_;
}
case 7:
{
lean_object* v_i_2482_; lean_object* v___x_2483_; 
v_i_2482_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2482_);
lean_dec_ref(v_x_2459_);
v___x_2483_ = l_Lean_Elab_FieldInfo_format(v_ctx_2458_, v_i_2482_);
return v___x_2483_;
}
case 8:
{
lean_object* v_i_2484_; lean_object* v___x_2485_; 
v_i_2484_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2484_);
lean_dec_ref(v_x_2459_);
v___x_2485_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2458_, v_i_2484_);
return v___x_2485_;
}
case 9:
{
lean_object* v_i_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v_ctx_2458_);
v_i_2486_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2488_ = v_x_2459_;
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_i_2486_);
lean_dec(v_x_2459_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2486_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2490_);
v___x_2492_ = v___x_2488_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
case 10:
{
lean_object* v_i_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_ctx_2458_);
v_i_2495_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2497_ = v_x_2459_;
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_i_2495_);
lean_dec(v_x_2459_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = l_Lean_Elab_CustomInfo_format(v_i_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2499_);
v___x_2501_ = v___x_2497_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
case 11:
{
lean_object* v_i_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v_ctx_2458_);
v_i_2504_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2506_ = v_x_2459_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_i_2504_);
lean_dec(v_x_2459_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2504_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
case 12:
{
lean_object* v_i_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2521_; 
v_i_2513_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2515_ = v_x_2459_;
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_i_2513_);
lean_dec(v_x_2459_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2458_, v_i_2513_);
lean_dec(v_i_2513_);
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
case 13:
{
lean_object* v_i_2522_; lean_object* v___x_2523_; 
v_i_2522_ = lean_ctor_get(v_x_2459_, 0);
lean_inc_ref(v_i_2522_);
lean_dec_ref(v_x_2459_);
v___x_2523_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2458_, v_i_2522_);
return v___x_2523_;
}
case 14:
{
lean_object* v_i_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_i_2524_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2526_ = v_x_2459_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_i_2524_);
lean_dec(v_x_2459_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2458_, v_i_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
case 15:
{
lean_object* v_i_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
v_i_2533_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2535_ = v_x_2459_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_i_2533_);
lean_dec(v_x_2459_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2537_ = l_Lean_Elab_DocInfo_format(v_ctx_2458_, v_i_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2537_);
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
default: 
{
lean_object* v_i_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2550_; 
v_i_2542_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2544_ = v_x_2459_;
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_i_2542_);
lean_dec(v_x_2459_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2546_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2458_, v_i_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set_tag(v___x_2544_, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2551_, lean_object* v_x_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Elab_Info_format(v_ctx_2551_, v_x_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2555_){
_start:
{
switch(lean_obj_tag(v_x_2555_))
{
case 0:
{
lean_object* v_i_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v_i_2556_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v_x_2555_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_i_2556_);
lean_dec(v_x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_toElabInfo_2560_; lean_object* v___x_2562_; 
v_toElabInfo_2560_ = lean_ctor_get(v_i_2556_, 0);
lean_inc_ref(v_toElabInfo_2560_);
lean_dec_ref(v_i_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
lean_ctor_set(v___x_2558_, 0, v_toElabInfo_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_toElabInfo_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
case 1:
{
lean_object* v_i_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_i_2565_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2567_ = v_x_2555_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_i_2565_);
lean_dec(v_x_2555_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_toElabInfo_2569_; lean_object* v___x_2571_; 
v_toElabInfo_2569_ = lean_ctor_get(v_i_2565_, 0);
lean_inc_ref(v_toElabInfo_2569_);
lean_dec_ref(v_i_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_toElabInfo_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_toElabInfo_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
case 2:
{
lean_object* v_i_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2582_; 
v_i_2574_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2576_ = v_x_2555_;
v_isShared_2577_ = v_isSharedCheck_2582_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_i_2574_);
lean_dec(v_x_2555_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2582_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_toElabInfo_2578_; lean_object* v___x_2580_; 
v_toElabInfo_2578_ = lean_ctor_get(v_i_2574_, 0);
lean_inc_ref(v_toElabInfo_2578_);
lean_dec_ref(v_i_2574_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 1);
lean_ctor_set(v___x_2576_, 0, v_toElabInfo_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_toElabInfo_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
case 3:
{
lean_object* v_i_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_i_2583_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v_x_2555_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_i_2583_);
lean_dec(v_x_2555_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_i_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
case 13:
{
lean_object* v_i_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2600_; 
v_i_2591_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2593_ = v_x_2555_;
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_i_2591_);
lean_dec(v_x_2555_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_toTermInfo_2595_; lean_object* v_toElabInfo_2596_; lean_object* v___x_2598_; 
v_toTermInfo_2595_ = lean_ctor_get(v_i_2591_, 0);
lean_inc_ref(v_toTermInfo_2595_);
lean_dec_ref(v_i_2591_);
v_toElabInfo_2596_ = lean_ctor_get(v_toTermInfo_2595_, 0);
lean_inc_ref(v_toElabInfo_2596_);
lean_dec_ref(v_toTermInfo_2595_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 0, v_toElabInfo_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_toElabInfo_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
case 14:
{
lean_object* v_i_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_i_2601_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v_x_2555_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_i_2601_);
lean_dec(v_x_2555_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_i_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
case 15:
{
lean_object* v_i_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_i_2609_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v_x_2555_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_i_2609_);
lean_dec(v_x_2555_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_i_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
case 16:
{
lean_object* v_i_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_i_2617_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v_x_2555_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_i_2617_);
lean_dec(v_x_2555_);
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
lean_ctor_set_tag(v___x_2619_, 1);
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
default: 
{
lean_object* v___x_2626_; 
lean_dec_ref(v_x_2555_);
v___x_2626_ = lean_box(0);
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
if (lean_obj_tag(v_x_2627_) == 1)
{
if (lean_obj_tag(v_x_2628_) == 0)
{
lean_object* v_val_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2664_; 
v_val_2629_ = lean_ctor_get(v_x_2627_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_x_2627_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2631_ = v_x_2627_;
v_isShared_2632_ = v_isSharedCheck_2664_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_val_2629_);
lean_dec(v_x_2627_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2664_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_toCommandContextInfo_2633_; lean_object* v_i_2634_; lean_object* v_parentDecl_x3f_2635_; lean_object* v_autoImplicits_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2662_; 
v_toCommandContextInfo_2633_ = lean_ctor_get(v_val_2629_, 0);
lean_inc_ref(v_toCommandContextInfo_2633_);
v_i_2634_ = lean_ctor_get(v_x_2628_, 0);
v_parentDecl_x3f_2635_ = lean_ctor_get(v_val_2629_, 1);
v_autoImplicits_2636_ = lean_ctor_get(v_val_2629_, 2);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_val_2629_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v_val_2629_, 0);
lean_dec(v_unused_2663_);
v___x_2638_ = v_val_2629_;
v_isShared_2639_ = v_isSharedCheck_2662_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_autoImplicits_2636_);
lean_inc(v_parentDecl_x3f_2635_);
lean_dec(v_val_2629_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2662_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_env_2640_; lean_object* v_cmdEnv_x3f_2641_; lean_object* v_fileMap_2642_; lean_object* v_options_2643_; lean_object* v_currNamespace_2644_; lean_object* v_openDecls_2645_; lean_object* v_ngen_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2660_; 
v_env_2640_ = lean_ctor_get(v_toCommandContextInfo_2633_, 0);
v_cmdEnv_x3f_2641_ = lean_ctor_get(v_toCommandContextInfo_2633_, 1);
v_fileMap_2642_ = lean_ctor_get(v_toCommandContextInfo_2633_, 2);
v_options_2643_ = lean_ctor_get(v_toCommandContextInfo_2633_, 4);
v_currNamespace_2644_ = lean_ctor_get(v_toCommandContextInfo_2633_, 5);
v_openDecls_2645_ = lean_ctor_get(v_toCommandContextInfo_2633_, 6);
v_ngen_2646_ = lean_ctor_get(v_toCommandContextInfo_2633_, 7);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_toCommandContextInfo_2633_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_toCommandContextInfo_2633_, 3);
lean_dec(v_unused_2661_);
v___x_2648_ = v_toCommandContextInfo_2633_;
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_ngen_2646_);
lean_inc(v_openDecls_2645_);
lean_inc(v_currNamespace_2644_);
lean_inc(v_options_2643_);
lean_inc(v_fileMap_2642_);
lean_inc(v_cmdEnv_x3f_2641_);
lean_inc(v_env_2640_);
lean_dec(v_toCommandContextInfo_2633_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_mctxAfter_2650_; lean_object* v___x_2652_; 
v_mctxAfter_2650_ = lean_ctor_get(v_i_2634_, 3);
lean_inc_ref(v_mctxAfter_2650_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 3, v_mctxAfter_2650_);
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_env_2640_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_cmdEnv_x3f_2641_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_fileMap_2642_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_mctxAfter_2650_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_options_2643_);
lean_ctor_set(v_reuseFailAlloc_2659_, 5, v_currNamespace_2644_);
lean_ctor_set(v_reuseFailAlloc_2659_, 6, v_openDecls_2645_);
lean_ctor_set(v_reuseFailAlloc_2659_, 7, v_ngen_2646_);
v___x_2652_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2652_);
v___x_2654_ = v___x_2638_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_parentDecl_x3f_2635_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_autoImplicits_2636_);
v___x_2654_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2654_);
v___x_2656_ = v___x_2631_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
}
else
{
return v_x_2627_;
}
}
else
{
return v_x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2665_, v_x_2666_);
lean_dec_ref(v_x_2666_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
if (lean_obj_tag(v_x_2669_) == 0)
{
return v_x_2668_;
}
else
{
lean_object* v_head_2670_; lean_object* v_tail_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_head_2670_ = lean_ctor_get(v_x_2669_, 0);
v_tail_2671_ = lean_ctor_get(v_x_2669_, 1);
v___x_2672_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2673_ = lean_string_append(v_x_2668_, v___x_2672_);
v___x_2674_ = lean_expr_dbg_to_string(v_head_2670_);
v___x_2675_ = lean_string_append(v___x_2673_, v___x_2674_);
lean_dec_ref(v___x_2674_);
v_x_2668_ = v___x_2675_;
v_x_2669_ = v_tail_2671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2677_, lean_object* v_x_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2677_, v_x_2678_);
lean_dec(v_x_2678_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2683_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2684_;
}
else
{
lean_object* v_tail_2685_; 
v_tail_2685_ = lean_ctor_get(v_x_2683_, 1);
if (lean_obj_tag(v_tail_2685_) == 0)
{
lean_object* v_head_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_head_2686_ = lean_ctor_get(v_x_2683_, 0);
v___x_2687_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2688_ = lean_expr_dbg_to_string(v_head_2686_);
v___x_2689_ = lean_string_append(v___x_2687_, v___x_2688_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2691_ = lean_string_append(v___x_2689_, v___x_2690_);
return v___x_2691_;
}
else
{
lean_object* v_head_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint32_t v___x_2697_; lean_object* v___x_2698_; 
v_head_2692_ = lean_ctor_get(v_x_2683_, 0);
v___x_2693_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2694_ = lean_expr_dbg_to_string(v_head_2692_);
v___x_2695_ = lean_string_append(v___x_2693_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2695_, v_tail_2685_);
v___x_2697_ = 93;
v___x_2698_ = lean_string_push(v___x_2696_, v___x_2697_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2699_);
lean_dec(v_x_2699_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2707_){
_start:
{
switch(lean_obj_tag(v_ctx_2707_))
{
case 0:
{
lean_object* v___x_2708_; 
lean_dec_ref(v_ctx_2707_);
v___x_2708_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2708_;
}
case 1:
{
lean_object* v_parentDecl_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2722_; 
v_parentDecl_2709_ = lean_ctor_get(v_ctx_2707_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_ctx_2707_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2711_ = v_ctx_2707_;
v_isShared_2712_ = v_isSharedCheck_2722_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_parentDecl_2709_);
lean_dec(v_ctx_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2722_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2713_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2714_ = 1;
v___x_2715_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2709_, v___x_2714_);
v___x_2716_ = lean_string_append(v___x_2713_, v___x_2715_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2718_ = lean_string_append(v___x_2716_, v___x_2717_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 3);
lean_ctor_set(v___x_2711_, 0, v___x_2718_);
v___x_2720_ = v___x_2711_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(3, 1, 0);
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
default: 
{
lean_object* v_autoImplicits_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2738_; 
v_autoImplicits_2723_ = lean_ctor_get(v_ctx_2707_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_ctx_2707_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2725_ = v_ctx_2707_;
v_isShared_2726_ = v_isSharedCheck_2738_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_autoImplicits_2723_);
lean_dec(v_ctx_2707_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2738_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2727_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2728_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2729_ = lean_array_to_list(v_autoImplicits_2723_);
v___x_2730_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2729_);
lean_dec(v___x_2729_);
v___x_2731_ = lean_string_append(v___x_2728_, v___x_2730_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = lean_string_append(v___x_2727_, v___x_2731_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2734_ = lean_string_append(v___x_2732_, v___x_2733_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 3);
lean_ctor_set(v___x_2725_, 0, v___x_2734_);
v___x_2736_ = v___x_2725_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2748_, lean_object* v_ctx_x3f_2749_){
_start:
{
switch(lean_obj_tag(v_tree_2748_))
{
case 0:
{
lean_object* v_i_2751_; lean_object* v_t_2752_; lean_object* v___x_2753_; 
v_i_2751_ = lean_ctor_get(v_tree_2748_, 0);
lean_inc_ref(v_i_2751_);
v_t_2752_ = lean_ctor_get(v_tree_2748_, 1);
lean_inc_ref(v_t_2752_);
lean_dec_ref(v_tree_2748_);
v___x_2753_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2751_, v_ctx_x3f_2749_);
v_tree_2748_ = v_t_2752_;
v_ctx_x3f_2749_ = v___x_2753_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2749_) == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec_ref(v_tree_2748_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
else
{
lean_object* v_i_2757_; lean_object* v_children_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2808_; 
v_i_2757_ = lean_ctor_get(v_tree_2748_, 0);
v_children_2758_ = lean_ctor_get(v_tree_2748_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_tree_2748_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2760_ = v_tree_2748_;
v_isShared_2761_ = v_isSharedCheck_2808_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_children_2758_);
lean_inc(v_i_2757_);
lean_dec(v_tree_2748_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2808_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
v_val_2762_ = lean_ctor_get(v_ctx_x3f_2749_, 0);
lean_inc_ref(v_i_2757_);
lean_inc(v_val_2762_);
v___x_2763_ = l_Lean_Elab_Info_format(v_val_2762_, v_i_2757_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2807_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2807_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2807_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_size_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_size_2768_ = lean_ctor_get(v_children_2758_, 2);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_nat_dec_eq(v_size_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_del_object(v___x_2766_);
v___x_2771_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2749_, v_i_2757_);
lean_dec_ref(v_i_2757_);
v___x_2772_ = l_Lean_PersistentArray_toList___redArg(v_children_2758_);
lean_dec_ref(v_children_2758_);
v___x_2773_ = lean_box(0);
v___x_2774_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2771_, v___x_2772_, v___x_2773_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2790_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 5);
lean_ctor_set(v___x_2760_, 1, v_a_2764_);
lean_ctor_set(v___x_2760_, 0, v___x_2779_);
v___x_2781_ = v___x_2760_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_a_2764_);
v___x_2781_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2782_ = lean_box(1);
v___x_2783_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2782_, v_a_2775_);
v___x_2784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2781_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Std_Format_nestD(v___x_2784_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2785_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2764_);
lean_del_object(v___x_2760_);
v_a_2791_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2774_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2774_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec_ref(v_children_2758_);
lean_dec_ref(v_i_2757_);
lean_dec_ref(v_ctx_x3f_2749_);
v___x_2799_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 5);
lean_ctor_set(v___x_2760_, 1, v_a_2764_);
lean_ctor_set(v___x_2760_, 0, v___x_2799_);
v___x_2801_ = v___x_2760_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2764_);
v___x_2801_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = l_Std_Format_nestD(v___x_2801_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2802_);
v___x_2804_ = v___x_2766_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
else
{
lean_del_object(v___x_2760_);
lean_dec_ref(v_children_2758_);
lean_dec_ref(v_i_2757_);
lean_dec_ref(v_ctx_x3f_2749_);
return v___x_2763_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_ctx_x3f_2749_);
v_mvarId_2809_ = lean_ctor_get(v_tree_2748_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_tree_2748_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2811_ = v_tree_2748_;
v_isShared_2812_ = v_isSharedCheck_2822_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_mvarId_2809_);
lean_dec(v_tree_2748_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2822_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; uint8_t v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2813_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2814_ = 1;
v___x_2815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2809_, v___x_2814_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 3);
lean_ctor_set(v___x_2811_, 0, v___x_2815_);
v___x_2817_ = v___x_2811_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2813_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = l_Std_Format_nestD(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v___x_2823_);
v___x_2827_ = l_List_reverse___redArg(v_x_2825_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
else
{
lean_object* v_head_2829_; lean_object* v_tail_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2848_; 
v_head_2829_ = lean_ctor_get(v_x_2824_, 0);
v_tail_2830_ = lean_ctor_get(v_x_2824_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_x_2824_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2832_ = v_x_2824_;
v_isShared_2833_ = v_isSharedCheck_2848_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_tail_2830_);
lean_inc(v_head_2829_);
lean_dec(v_x_2824_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2848_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; 
lean_inc(v___x_2823_);
v___x_2834_ = l_Lean_Elab_InfoTree_format(v_head_2829_, v___x_2823_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2834_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 1, v_x_2825_);
lean_ctor_set(v___x_2832_, 0, v_a_2835_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2835_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_x_2825_);
v___x_2837_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
v_x_2824_ = v_tail_2830_;
v_x_2825_ = v___x_2837_;
goto _start;
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_x_2825_);
lean_dec(v___x_2823_);
v_a_2840_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2834_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2834_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2849_, lean_object* v_x_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2849_, v_x_2850_, v_x_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2854_, lean_object* v_ctx_x3f_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Elab_InfoTree_format(v_tree_2854_, v_ctx_x3f_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2858_, lean_object* v_s_2859_){
_start:
{
uint8_t v_enabled_2860_; lean_object* v_assignment_2861_; lean_object* v_lazyAssignment_2862_; lean_object* v_trees_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
v_enabled_2860_ = lean_ctor_get_uint8(v_s_2859_, sizeof(void*)*3);
v_assignment_2861_ = lean_ctor_get(v_s_2859_, 0);
v_lazyAssignment_2862_ = lean_ctor_get(v_s_2859_, 1);
v_trees_2863_ = lean_ctor_get(v_s_2859_, 2);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_s_2859_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2865_ = v_s_2859_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_trees_2863_);
lean_inc(v_lazyAssignment_2862_);
lean_inc(v_assignment_2861_);
lean_dec(v_s_2859_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_apply_1(v_f_2858_, v_trees_2863_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 2, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_assignment_2861_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_lazyAssignment_2862_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v___x_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*3, v_enabled_2860_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2872_, lean_object* v_f_2873_){
_start:
{
lean_object* v_modifyInfoState_2874_; lean_object* v___f_2875_; lean_object* v___x_2876_; 
v_modifyInfoState_2874_ = lean_ctor_get(v_inst_2872_, 1);
lean_inc(v_modifyInfoState_2874_);
lean_dec_ref(v_inst_2872_);
v___f_2875_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2875_, 0, v_f_2873_);
v___x_2876_ = lean_apply_1(v_modifyInfoState_2874_, v___f_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2877_, lean_object* v_inst_2878_, lean_object* v_f_2879_){
_start:
{
lean_object* v_modifyInfoState_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; 
v_modifyInfoState_2880_ = lean_ctor_get(v_inst_2878_, 1);
lean_inc(v_modifyInfoState_2880_);
lean_dec_ref(v_inst_2878_);
v___f_2881_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2881_, 0, v_f_2879_);
v___x_2882_ = lean_apply_1(v_modifyInfoState_2880_, v___f_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_unsigned_to_nat(32u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2886_ = ((size_t)5ULL);
v___x_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = lean_unsigned_to_nat(32u);
v___x_2889_ = lean_mk_empty_array_with_capacity(v___x_2888_);
v___x_2890_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2891_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v___x_2889_);
lean_ctor_set(v___x_2891_, 2, v___x_2887_);
lean_ctor_set(v___x_2891_, 3, v___x_2887_);
lean_ctor_set_usize(v___x_2891_, 4, v___x_2886_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2892_){
_start:
{
uint8_t v_enabled_2893_; lean_object* v_assignment_2894_; lean_object* v_lazyAssignment_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
v_enabled_2893_ = lean_ctor_get_uint8(v_s_2892_, sizeof(void*)*3);
v_assignment_2894_ = lean_ctor_get(v_s_2892_, 0);
v_lazyAssignment_2895_ = lean_ctor_get(v_s_2892_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_s_2892_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v_s_2892_, 2);
lean_dec(v_unused_2904_);
v___x_2897_ = v_s_2892_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_lazyAssignment_2895_);
lean_inc(v_assignment_2894_);
lean_dec(v_s_2892_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 2, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_assignment_2894_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_lazyAssignment_2895_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v___x_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*3, v_enabled_2893_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2905_, lean_object* v_trees_2906_, lean_object* v_____r_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_apply_2(v_toPure_2905_, lean_box(0), v_trees_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2909_, lean_object* v_modifyInfoState_2910_, lean_object* v___f_2911_, lean_object* v_toBind_2912_, lean_object* v_____do__lift_2913_){
_start:
{
lean_object* v_trees_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_trees_2914_ = lean_ctor_get(v_____do__lift_2913_, 2);
lean_inc_ref(v_trees_2914_);
lean_dec_ref(v_____do__lift_2913_);
v___f_2915_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2915_, 0, v_toPure_2909_);
lean_closure_set(v___f_2915_, 1, v_trees_2914_);
v___x_2916_ = lean_apply_1(v_modifyInfoState_2910_, v___f_2911_);
v___x_2917_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v___x_2916_, v___f_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2919_, lean_object* v_inst_2920_){
_start:
{
lean_object* v_toApplicative_2921_; lean_object* v_toBind_2922_; lean_object* v_getInfoState_2923_; lean_object* v_modifyInfoState_2924_; lean_object* v_toPure_2925_; lean_object* v___f_2926_; lean_object* v___f_2927_; lean_object* v___x_2928_; 
v_toApplicative_2921_ = lean_ctor_get(v_inst_2919_, 0);
lean_inc_ref(v_toApplicative_2921_);
v_toBind_2922_ = lean_ctor_get(v_inst_2919_, 1);
lean_inc_n(v_toBind_2922_, 2);
lean_dec_ref(v_inst_2919_);
v_getInfoState_2923_ = lean_ctor_get(v_inst_2920_, 0);
lean_inc(v_getInfoState_2923_);
v_modifyInfoState_2924_ = lean_ctor_get(v_inst_2920_, 1);
lean_inc(v_modifyInfoState_2924_);
lean_dec_ref(v_inst_2920_);
v_toPure_2925_ = lean_ctor_get(v_toApplicative_2921_, 1);
lean_inc(v_toPure_2925_);
lean_dec_ref(v_toApplicative_2921_);
v___f_2926_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2927_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2927_, 0, v_toPure_2925_);
lean_closure_set(v___f_2927_, 1, v_modifyInfoState_2924_);
lean_closure_set(v___f_2927_, 2, v___f_2926_);
lean_closure_set(v___f_2927_, 3, v_toBind_2922_);
v___x_2928_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v_getInfoState_2923_, v___f_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2929_, lean_object* v_inst_2930_, lean_object* v_inst_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2930_, v_inst_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2933_, lean_object* v_s_2934_){
_start:
{
uint8_t v_enabled_2935_; lean_object* v_assignment_2936_; lean_object* v_lazyAssignment_2937_; lean_object* v_trees_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2946_; 
v_enabled_2935_ = lean_ctor_get_uint8(v_s_2934_, sizeof(void*)*3);
v_assignment_2936_ = lean_ctor_get(v_s_2934_, 0);
v_lazyAssignment_2937_ = lean_ctor_get(v_s_2934_, 1);
v_trees_2938_ = lean_ctor_get(v_s_2934_, 2);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_s_2934_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2940_ = v_s_2934_;
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_trees_2938_);
lean_inc(v_lazyAssignment_2937_);
lean_inc(v_assignment_2936_);
lean_dec(v_s_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = l_Lean_PersistentArray_push___redArg(v_trees_2938_, v_t_2933_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 2, v___x_2942_);
v___x_2944_ = v___x_2940_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_assignment_2936_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_lazyAssignment_2937_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v___x_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2945_, sizeof(void*)*3, v_enabled_2935_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2947_, lean_object* v_modifyInfoState_2948_, lean_object* v___f_2949_, lean_object* v_____do__lift_2950_){
_start:
{
uint8_t v_enabled_2951_; 
v_enabled_2951_ = lean_ctor_get_uint8(v_____do__lift_2950_, sizeof(void*)*3);
if (v_enabled_2951_ == 0)
{
lean_object* v_toPure_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v___f_2949_);
lean_dec(v_modifyInfoState_2948_);
v_toPure_2952_ = lean_ctor_get(v_toApplicative_2947_, 1);
lean_inc(v_toPure_2952_);
lean_dec_ref(v_toApplicative_2947_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2953_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; 
lean_dec_ref(v_toApplicative_2947_);
v___x_2955_ = lean_apply_1(v_modifyInfoState_2948_, v___f_2949_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_2956_, lean_object* v_modifyInfoState_2957_, lean_object* v___f_2958_, lean_object* v_____do__lift_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_2956_, v_modifyInfoState_2957_, v___f_2958_, v_____do__lift_2959_);
lean_dec_ref(v_____do__lift_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_t_2963_){
_start:
{
lean_object* v_toApplicative_2964_; lean_object* v_toBind_2965_; lean_object* v_getInfoState_2966_; lean_object* v_modifyInfoState_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; 
v_toApplicative_2964_ = lean_ctor_get(v_inst_2961_, 0);
lean_inc_ref(v_toApplicative_2964_);
v_toBind_2965_ = lean_ctor_get(v_inst_2961_, 1);
lean_inc(v_toBind_2965_);
lean_dec_ref(v_inst_2961_);
v_getInfoState_2966_ = lean_ctor_get(v_inst_2962_, 0);
lean_inc(v_getInfoState_2966_);
v_modifyInfoState_2967_ = lean_ctor_get(v_inst_2962_, 1);
lean_inc(v_modifyInfoState_2967_);
lean_dec_ref(v_inst_2962_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2968_, 0, v_t_2963_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2969_, 0, v_toApplicative_2964_);
lean_closure_set(v___f_2969_, 1, v_modifyInfoState_2967_);
lean_closure_set(v___f_2969_, 2, v___f_2968_);
v___x_2970_ = lean_apply_4(v_toBind_2965_, lean_box(0), lean_box(0), v_getInfoState_2966_, v___f_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_t_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2972_, v_inst_2973_, v_t_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_2976_, lean_object* v_t_2977_, lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_____do__lift_2980_){
_start:
{
uint8_t v_enabled_2981_; 
v_enabled_2981_ = lean_ctor_get_uint8(v_____do__lift_2980_, sizeof(void*)*3);
if (v_enabled_2981_ == 0)
{
lean_object* v_toPure_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec_ref(v_inst_2979_);
lean_dec_ref(v_inst_2978_);
lean_dec_ref(v_t_2977_);
v_toPure_2982_ = lean_ctor_get(v_toApplicative_2976_, 1);
lean_inc(v_toPure_2982_);
lean_dec_ref(v_toApplicative_2976_);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_apply_2(v_toPure_2982_, lean_box(0), v___x_2983_);
return v___x_2984_;
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v_toApplicative_2976_);
v___x_2985_ = lean_unsigned_to_nat(32u);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2985_);
lean_dec_ref(v___x_2986_);
v___x_2987_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_t_2977_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2978_, v_inst_2979_, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_2990_, lean_object* v_t_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_____do__lift_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_2990_, v_t_2991_, v_inst_2992_, v_inst_2993_, v_____do__lift_2994_);
lean_dec_ref(v_____do__lift_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_t_2998_){
_start:
{
lean_object* v_toApplicative_2999_; lean_object* v_toBind_3000_; lean_object* v_getInfoState_3001_; lean_object* v___f_3002_; lean_object* v___x_3003_; 
v_toApplicative_2999_ = lean_ctor_get(v_inst_2996_, 0);
lean_inc_ref(v_toApplicative_2999_);
v_toBind_3000_ = lean_ctor_get(v_inst_2996_, 1);
lean_inc(v_toBind_3000_);
v_getInfoState_3001_ = lean_ctor_get(v_inst_2997_, 0);
lean_inc(v_getInfoState_3001_);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3002_, 0, v_toApplicative_2999_);
lean_closure_set(v___f_3002_, 1, v_t_2998_);
lean_closure_set(v___f_3002_, 2, v_inst_2996_);
lean_closure_set(v___f_3002_, 3, v_inst_2997_);
v___x_3003_ = lean_apply_4(v_toBind_3000_, lean_box(0), lean_box(0), v_getInfoState_3001_, v___f_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_t_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3005_, v_inst_3006_, v_t_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_info_3011_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_info_3011_);
v___x_3013_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3009_, v_inst_3010_, v___x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_info_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3015_, v_inst_3016_, v_info_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3019_, lean_object* v_expectedType_x3f_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_____do__lift_3023_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v_stx_3019_);
v___x_3026_ = l_Lean_LocalContext_empty;
v___x_3027_ = 0;
v___x_3028_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3028_, 0, v___x_3025_);
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
lean_ctor_set(v___x_3028_, 2, v_expectedType_x3f_3020_);
lean_ctor_set(v___x_3028_, 3, v_____do__lift_3023_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*4, v___x_3027_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*4 + 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
v___x_3030_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3021_, v_inst_3022_, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_stx_3035_, lean_object* v_n_3036_, lean_object* v_expectedType_x3f_3037_){
_start:
{
lean_object* v_toBind_3038_; lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_toBind_3038_ = lean_ctor_get(v_inst_3031_, 1);
lean_inc(v_toBind_3038_);
lean_inc_ref(v_inst_3031_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3039_, 0, v_stx_3035_);
lean_closure_set(v___f_3039_, 1, v_expectedType_x3f_3037_);
lean_closure_set(v___f_3039_, 2, v_inst_3031_);
lean_closure_set(v___f_3039_, 3, v_inst_3032_);
v___x_3040_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3031_, v_inst_3033_, v_inst_3034_, v_n_3036_);
v___x_3041_ = lean_apply_4(v_toBind_3038_, lean_box(0), lean_box(0), v___x_3040_, v___f_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_stx_3047_, lean_object* v_n_3048_, lean_object* v_expectedType_x3f_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3043_, v_inst_3044_, v_inst_3045_, v_inst_3046_, v_stx_3047_, v_n_3048_, v_expectedType_x3f_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v_infoState_3055_; uint8_t v_enabled_3056_; 
v___x_3054_ = lean_st_ref_get(v___y_3052_);
v_infoState_3055_ = lean_ctor_get(v___x_3054_, 7);
lean_inc_ref(v_infoState_3055_);
lean_dec(v___x_3054_);
v_enabled_3056_ = lean_ctor_get_uint8(v_infoState_3055_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3055_);
if (v_enabled_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_t_3051_);
v___x_3057_ = lean_box(0);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v_infoState_3060_; lean_object* v_env_3061_; lean_object* v_nextMacroScope_3062_; lean_object* v_ngen_3063_; lean_object* v_auxDeclNGen_3064_; lean_object* v_traceState_3065_; lean_object* v_cache_3066_; lean_object* v_messages_3067_; lean_object* v_snapshotTasks_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3090_; 
v___x_3059_ = lean_st_ref_take(v___y_3052_);
v_infoState_3060_ = lean_ctor_get(v___x_3059_, 7);
v_env_3061_ = lean_ctor_get(v___x_3059_, 0);
v_nextMacroScope_3062_ = lean_ctor_get(v___x_3059_, 1);
v_ngen_3063_ = lean_ctor_get(v___x_3059_, 2);
v_auxDeclNGen_3064_ = lean_ctor_get(v___x_3059_, 3);
v_traceState_3065_ = lean_ctor_get(v___x_3059_, 4);
v_cache_3066_ = lean_ctor_get(v___x_3059_, 5);
v_messages_3067_ = lean_ctor_get(v___x_3059_, 6);
v_snapshotTasks_3068_ = lean_ctor_get(v___x_3059_, 8);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3070_ = v___x_3059_;
v_isShared_3071_ = v_isSharedCheck_3090_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_snapshotTasks_3068_);
lean_inc(v_infoState_3060_);
lean_inc(v_messages_3067_);
lean_inc(v_cache_3066_);
lean_inc(v_traceState_3065_);
lean_inc(v_auxDeclNGen_3064_);
lean_inc(v_ngen_3063_);
lean_inc(v_nextMacroScope_3062_);
lean_inc(v_env_3061_);
lean_dec(v___x_3059_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3090_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
uint8_t v_enabled_3072_; lean_object* v_assignment_3073_; lean_object* v_lazyAssignment_3074_; lean_object* v_trees_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3089_; 
v_enabled_3072_ = lean_ctor_get_uint8(v_infoState_3060_, sizeof(void*)*3);
v_assignment_3073_ = lean_ctor_get(v_infoState_3060_, 0);
v_lazyAssignment_3074_ = lean_ctor_get(v_infoState_3060_, 1);
v_trees_3075_ = lean_ctor_get(v_infoState_3060_, 2);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_infoState_3060_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3077_ = v_infoState_3060_;
v_isShared_3078_ = v_isSharedCheck_3089_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_trees_3075_);
lean_inc(v_lazyAssignment_3074_);
lean_inc(v_assignment_3073_);
lean_dec(v_infoState_3060_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3089_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = l_Lean_PersistentArray_push___redArg(v_trees_3075_, v_t_3051_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 2, v___x_3079_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_assignment_3073_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_lazyAssignment_3074_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v___x_3079_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*3, v_enabled_3072_);
v___x_3081_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3083_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 7, v___x_3081_);
v___x_3083_ = v___x_3070_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_env_3061_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_nextMacroScope_3062_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_ngen_3063_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_auxDeclNGen_3064_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_traceState_3065_);
lean_ctor_set(v_reuseFailAlloc_3087_, 5, v_cache_3066_);
lean_ctor_set(v_reuseFailAlloc_3087_, 6, v_messages_3067_);
lean_ctor_set(v_reuseFailAlloc_3087_, 7, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3087_, 8, v_snapshotTasks_3068_);
v___x_3083_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_st_ref_set(v___y_3052_, v___x_3083_);
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3091_, v___y_3092_);
lean_dec(v___y_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; lean_object* v_infoState_3100_; uint8_t v_enabled_3101_; 
v___x_3099_ = lean_st_ref_get(v___y_3097_);
v_infoState_3100_ = lean_ctor_get(v___x_3099_, 7);
lean_inc_ref(v_infoState_3100_);
lean_dec(v___x_3099_);
v_enabled_3101_ = lean_ctor_get_uint8(v_infoState_3100_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3100_);
if (v_enabled_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref(v_t_3095_);
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3104_ = lean_unsigned_to_nat(32u);
v___x_3105_ = lean_mk_empty_array_with_capacity(v___x_3104_);
lean_dec_ref(v___x_3105_);
v___x_3106_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_t_3095_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3107_, v___y_3097_);
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
lean_ctor_set(v___x_3119_, 2, v___x_3118_);
lean_ctor_set(v___x_3119_, 3, v___x_3118_);
lean_ctor_set(v___x_3119_, 4, v___x_3117_);
lean_ctor_set(v___x_3119_, 5, v___x_3117_);
lean_ctor_set(v___x_3119_, 6, v___x_3117_);
lean_ctor_set(v___x_3119_, 7, v___x_3117_);
lean_ctor_set(v___x_3119_, 8, v___x_3117_);
lean_ctor_set(v___x_3119_, 9, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3120_ = lean_box(1);
v___x_3121_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___x_3121_);
lean_ctor_set(v___x_3123_, 2, v___x_3120_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3132_ = l_Lean_stringToMessageData(v___x_3131_);
return v___x_3132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3145_, lean_object* v_declHint_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v_env_3150_; uint8_t v___x_3151_; 
v___x_3149_ = lean_st_ref_get(v___y_3147_);
v_env_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc_ref(v_env_3150_);
lean_dec(v___x_3149_);
v___x_3151_ = l_Lean_Name_isAnonymous(v_declHint_3146_);
if (v___x_3151_ == 0)
{
uint8_t v_isExporting_3152_; 
v_isExporting_3152_ = lean_ctor_get_uint8(v_env_3150_, sizeof(void*)*8);
if (v_isExporting_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec_ref(v_env_3150_);
lean_dec(v_declHint_3146_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_msg_3145_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
lean_inc_ref(v_env_3150_);
v___x_3154_ = l_Lean_Environment_setExporting(v_env_3150_, v___x_3151_);
lean_inc(v_declHint_3146_);
lean_inc_ref(v___x_3154_);
v___x_3155_ = l_Lean_Environment_contains(v___x_3154_, v_declHint_3146_, v_isExporting_3152_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_env_3150_);
lean_dec(v_declHint_3146_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_msg_3145_);
return v___x_3156_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v_c_3162_; lean_object* v___x_3163_; 
v___x_3157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3159_ = l_Lean_Options_empty;
v___x_3160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3154_);
lean_ctor_set(v___x_3160_, 1, v___x_3157_);
lean_ctor_set(v___x_3160_, 2, v___x_3158_);
lean_ctor_set(v___x_3160_, 3, v___x_3159_);
lean_inc(v_declHint_3146_);
v___x_3161_ = l_Lean_MessageData_ofConstName(v_declHint_3146_, v___x_3151_);
v_c_3162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3162_, 0, v___x_3160_);
lean_ctor_set(v_c_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3150_, v_declHint_3146_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v_env_3150_);
lean_dec(v_declHint_3146_);
v___x_3164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v_c_3162_);
v___x_3166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_MessageData_note(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_msg_3145_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
return v___x_3170_;
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3206_; 
v_val_3171_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3173_ = v___x_3163_;
v_isShared_3174_ = v_isSharedCheck_3206_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_val_3171_);
lean_dec(v___x_3163_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3206_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v_mod_3178_; uint8_t v___x_3179_; 
v___x_3175_ = lean_box(0);
v___x_3176_ = l_Lean_Environment_header(v_env_3150_);
lean_dec_ref(v_env_3150_);
v___x_3177_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3176_);
v_mod_3178_ = lean_array_get(v___x_3175_, v___x_3177_, v_val_3171_);
lean_dec(v_val_3171_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = l_Lean_isPrivateName(v_declHint_3146_);
lean_dec(v_declHint_3146_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v_c_3162_);
v___x_3182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Lean_MessageData_ofName(v_mod_3178_);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_MessageData_note(v___x_3187_);
v___x_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_msg_3145_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3189_);
v___x_3191_ = v___x_3173_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v_c_3162_);
v___x_3195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Lean_MessageData_ofName(v_mod_3178_);
v___x_3198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_MessageData_note(v___x_3200_);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_msg_3145_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3202_);
v___x_3204_ = v___x_3173_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3207_; 
lean_dec_ref(v_env_3150_);
lean_dec(v_declHint_3146_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_msg_3145_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3208_, lean_object* v_declHint_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3208_, v_declHint_3209_, v___y_3210_);
lean_dec(v___y_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3213_, lean_object* v_declHint_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3228_; 
v___x_3218_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3213_, v_declHint_3214_, v___y_3216_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3223_ = l_Lean_unknownIdentifierMessageTag;
v___x_3224_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v_a_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3224_);
v___x_3226_ = v___x_3221_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3229_, lean_object* v_declHint_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3229_, v_declHint_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v_env_3240_; lean_object* v_options_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3239_ = lean_st_ref_get(v___y_3237_);
v_env_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_ref(v_env_3240_);
lean_dec(v___x_3239_);
v_options_3241_ = lean_ctor_get(v___y_3236_, 2);
v___x_3242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3243_ = lean_unsigned_to_nat(32u);
v___x_3244_ = lean_mk_empty_array_with_capacity(v___x_3243_);
lean_dec_ref(v___x_3244_);
v___x_3245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3241_);
v___x_3246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3246_, 0, v_env_3240_);
lean_ctor_set(v___x_3246_, 1, v___x_3242_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
lean_ctor_set(v___x_3246_, 3, v_options_3241_);
v___x_3247_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set(v___x_3247_, 1, v_msgData_3235_);
v___x_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_ref_3258_; lean_object* v___x_3259_; lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
v_ref_3258_ = lean_ctor_get(v___y_3255_, 5);
v___x_3259_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3254_, v___y_3255_, v___y_3256_);
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
lean_inc(v_ref_3258_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v_ref_3258_);
lean_ctor_set(v___x_3264_, 1, v_a_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 1);
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3274_, lean_object* v_msg_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_fileName_3279_; lean_object* v_fileMap_3280_; lean_object* v_options_3281_; lean_object* v_currRecDepth_3282_; lean_object* v_maxRecDepth_3283_; lean_object* v_ref_3284_; lean_object* v_currNamespace_3285_; lean_object* v_openDecls_3286_; lean_object* v_initHeartbeats_3287_; lean_object* v_maxHeartbeats_3288_; lean_object* v_quotContext_3289_; lean_object* v_currMacroScope_3290_; uint8_t v_diag_3291_; lean_object* v_cancelTk_x3f_3292_; uint8_t v_suppressElabErrors_3293_; lean_object* v_inheritedTraceOptions_3294_; lean_object* v_ref_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_fileName_3279_ = lean_ctor_get(v___y_3276_, 0);
v_fileMap_3280_ = lean_ctor_get(v___y_3276_, 1);
v_options_3281_ = lean_ctor_get(v___y_3276_, 2);
v_currRecDepth_3282_ = lean_ctor_get(v___y_3276_, 3);
v_maxRecDepth_3283_ = lean_ctor_get(v___y_3276_, 4);
v_ref_3284_ = lean_ctor_get(v___y_3276_, 5);
v_currNamespace_3285_ = lean_ctor_get(v___y_3276_, 6);
v_openDecls_3286_ = lean_ctor_get(v___y_3276_, 7);
v_initHeartbeats_3287_ = lean_ctor_get(v___y_3276_, 8);
v_maxHeartbeats_3288_ = lean_ctor_get(v___y_3276_, 9);
v_quotContext_3289_ = lean_ctor_get(v___y_3276_, 10);
v_currMacroScope_3290_ = lean_ctor_get(v___y_3276_, 11);
v_diag_3291_ = lean_ctor_get_uint8(v___y_3276_, sizeof(void*)*14);
v_cancelTk_x3f_3292_ = lean_ctor_get(v___y_3276_, 12);
v_suppressElabErrors_3293_ = lean_ctor_get_uint8(v___y_3276_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3294_ = lean_ctor_get(v___y_3276_, 13);
v_ref_3295_ = l_Lean_replaceRef(v_ref_3274_, v_ref_3284_);
lean_inc_ref(v_inheritedTraceOptions_3294_);
lean_inc(v_cancelTk_x3f_3292_);
lean_inc(v_currMacroScope_3290_);
lean_inc(v_quotContext_3289_);
lean_inc(v_maxHeartbeats_3288_);
lean_inc(v_initHeartbeats_3287_);
lean_inc(v_openDecls_3286_);
lean_inc(v_currNamespace_3285_);
lean_inc(v_maxRecDepth_3283_);
lean_inc(v_currRecDepth_3282_);
lean_inc_ref(v_options_3281_);
lean_inc_ref(v_fileMap_3280_);
lean_inc_ref(v_fileName_3279_);
v___x_3296_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3296_, 0, v_fileName_3279_);
lean_ctor_set(v___x_3296_, 1, v_fileMap_3280_);
lean_ctor_set(v___x_3296_, 2, v_options_3281_);
lean_ctor_set(v___x_3296_, 3, v_currRecDepth_3282_);
lean_ctor_set(v___x_3296_, 4, v_maxRecDepth_3283_);
lean_ctor_set(v___x_3296_, 5, v_ref_3295_);
lean_ctor_set(v___x_3296_, 6, v_currNamespace_3285_);
lean_ctor_set(v___x_3296_, 7, v_openDecls_3286_);
lean_ctor_set(v___x_3296_, 8, v_initHeartbeats_3287_);
lean_ctor_set(v___x_3296_, 9, v_maxHeartbeats_3288_);
lean_ctor_set(v___x_3296_, 10, v_quotContext_3289_);
lean_ctor_set(v___x_3296_, 11, v_currMacroScope_3290_);
lean_ctor_set(v___x_3296_, 12, v_cancelTk_x3f_3292_);
lean_ctor_set(v___x_3296_, 13, v_inheritedTraceOptions_3294_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*14, v_diag_3291_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*14 + 1, v_suppressElabErrors_3293_);
v___x_3297_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3275_, v___x_3296_, v___y_3277_);
lean_dec_ref(v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3298_, lean_object* v_msg_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3298_, v_msg_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v_ref_3298_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3304_, lean_object* v_msg_3305_, lean_object* v_declHint_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v___x_3312_; 
v___x_3310_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3305_, v_declHint_3306_, v___y_3307_, v___y_3308_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3304_, v_a_3311_, v___y_3307_, v___y_3308_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3313_, lean_object* v_msg_3314_, lean_object* v_declHint_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3313_, v_msg_3314_, v_declHint_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v_ref_3313_);
return v_res_3319_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3326_, lean_object* v_constName_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3331_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3332_ = 0;
lean_inc(v_constName_3327_);
v___x_3333_ = l_Lean_MessageData_ofConstName(v_constName_3327_, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3331_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3326_, v___x_3336_, v_constName_3327_, v___y_3328_, v___y_3329_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3338_, lean_object* v_constName_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3338_, v_constName_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v_ref_3338_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_ref_3348_; lean_object* v___x_3349_; 
v_ref_3348_ = lean_ctor_get(v___y_3345_, 5);
v___x_3349_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3348_, v_constName_3344_, v___y_3345_, v___y_3346_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v_env_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3359_ = lean_st_ref_get(v___y_3357_);
v_env_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_ref(v_env_3360_);
lean_dec(v___x_3359_);
v___x_3361_ = 0;
lean_inc(v_constName_3355_);
v___x_3362_ = l_Lean_Environment_findConstVal_x3f(v_env_3360_, v_constName_3355_, v___x_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3355_, v___y_3356_, v___y_3357_);
return v___x_3363_;
}
else
{
lean_object* v_val_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec(v_constName_3355_);
v_val_3364_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3362_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_val_3364_);
lean_dec(v___x_3362_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 0);
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_val_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
if (lean_obj_tag(v_a_3377_) == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = l_List_reverse___redArg(v_a_3378_);
return v___x_3379_;
}
else
{
lean_object* v_head_3380_; lean_object* v_tail_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3390_; 
v_head_3380_ = lean_ctor_get(v_a_3377_, 0);
v_tail_3381_ = lean_ctor_get(v_a_3377_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3383_ = v_a_3377_;
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_tail_3381_);
lean_inc(v_head_3380_);
lean_dec(v_a_3377_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = l_Lean_mkLevelParam(v_head_3380_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 1, v_a_3378_);
lean_ctor_set(v___x_3383_, 0, v___x_3385_);
v___x_3387_ = v___x_3383_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3378_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
v_a_3377_ = v_tail_3381_;
v_a_3378_ = v___x_3387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
lean_inc(v_constName_3391_);
v___x_3395_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3407_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3407_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3407_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_levelParams_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v_levelParams_3400_ = lean_ctor_get(v_a_3396_, 1);
lean_inc(v_levelParams_3400_);
lean_dec(v_a_3396_);
v___x_3401_ = lean_box(0);
v___x_3402_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3400_, v___x_3401_);
v___x_3403_ = l_Lean_mkConst(v_constName_3391_, v___x_3402_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3403_);
v___x_3405_ = v___x_3398_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v_constName_3391_);
v_a_3408_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3395_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3395_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3421_, lean_object* v_n_3422_, lean_object* v_expectedType_x3f_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3422_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = lean_box(0);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v_stx_3421_);
v___x_3431_ = l_Lean_LocalContext_empty;
v___x_3432_ = 0;
v___x_3433_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3433_, 0, v___x_3430_);
lean_ctor_set(v___x_3433_, 1, v___x_3431_);
lean_ctor_set(v___x_3433_, 2, v_expectedType_x3f_3423_);
lean_ctor_set(v___x_3433_, 3, v_a_3428_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*4, v___x_3432_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*4 + 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3434_, v___y_3424_, v___y_3425_);
return v___x_3435_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_expectedType_x3f_3423_);
lean_dec(v_stx_3421_);
v_a_3436_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3427_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3427_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3444_, lean_object* v_n_3445_, lean_object* v_expectedType_x3f_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3444_, v_n_3445_, v_expectedType_x3f_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3451_, lean_object* v_expectedType_x3f_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___x_3456_; 
lean_inc(v_id_3451_);
v___x_3456_ = l_Lean_realizeGlobalConstNoOverload(v_id_3451_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3484_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3484_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3484_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v_infoState_3462_; uint8_t v_enabled_3463_; 
v___x_3461_ = lean_st_ref_get(v_a_3454_);
v_infoState_3462_ = lean_ctor_get(v___x_3461_, 7);
lean_inc_ref(v_infoState_3462_);
lean_dec(v___x_3461_);
v_enabled_3463_ = lean_ctor_get_uint8(v_infoState_3462_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3462_);
if (v_enabled_3463_ == 0)
{
lean_object* v___x_3465_; 
lean_dec(v_expectedType_x3f_3452_);
lean_dec(v_id_3451_);
if (v_isShared_3460_ == 0)
{
v___x_3465_ = v___x_3459_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3457_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
else
{
lean_object* v___x_3467_; 
lean_del_object(v___x_3459_);
lean_inc(v_a_3457_);
v___x_3467_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3451_, v_a_3457_, v_expectedType_x3f_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3475_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_a_3457_);
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3457_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_a_3457_);
v_a_3476_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3467_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3467_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3452_);
lean_dec(v_id_3451_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3485_, lean_object* v_expectedType_x3f_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3485_, v_expectedType_x3f_3486_, v_a_3487_, v_a_3488_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3491_, v___y_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3501_, lean_object* v_constName_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3502_, v___y_3503_, v___y_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3507_, lean_object* v_constName_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3507_, v_constName_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3513_, lean_object* v_ref_3514_, lean_object* v_constName_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3514_, v_constName_3515_, v___y_3516_, v___y_3517_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3520_, lean_object* v_ref_3521_, lean_object* v_constName_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3520_, v_ref_3521_, v_constName_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v_ref_3521_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3527_, lean_object* v_ref_3528_, lean_object* v_msg_3529_, lean_object* v_declHint_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3528_, v_msg_3529_, v_declHint_3530_, v___y_3531_, v___y_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3535_, lean_object* v_ref_3536_, lean_object* v_msg_3537_, lean_object* v_declHint_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3535_, v_ref_3536_, v_msg_3537_, v_declHint_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v_ref_3536_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3543_, lean_object* v_declHint_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3543_, v_declHint_3544_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3549_, lean_object* v_declHint_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3549_, v_declHint_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3555_, lean_object* v_ref_3556_, lean_object* v_msg_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3556_, v_msg_3557_, v___y_3558_, v___y_3559_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3562_, lean_object* v_ref_3563_, lean_object* v_msg_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3562_, v_ref_3563_, v_msg_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v_ref_3563_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3569_, lean_object* v_msg_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3570_, v___y_3571_, v___y_3572_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3575_, lean_object* v_msg_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3575_, v_msg_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3581_, lean_object* v_expectedType_x3f_3582_, lean_object* v_as_x27_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
if (lean_obj_tag(v_as_x27_3583_) == 0)
{
lean_object* v___x_3588_; 
lean_dec(v_expectedType_x3f_3582_);
lean_dec(v_id_3581_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_b_3584_);
return v___x_3588_;
}
else
{
lean_object* v_head_3589_; lean_object* v_tail_3590_; lean_object* v___x_3591_; 
v_head_3589_ = lean_ctor_get(v_as_x27_3583_, 0);
v_tail_3590_ = lean_ctor_get(v_as_x27_3583_, 1);
lean_inc(v_expectedType_x3f_3582_);
lean_inc(v_head_3589_);
lean_inc(v_id_3581_);
v___x_3591_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3581_, v_head_3589_, v_expectedType_x3f_3582_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; 
lean_dec_ref(v___x_3591_);
v___x_3592_ = lean_box(0);
v_as_x27_3583_ = v_tail_3590_;
v_b_3584_ = v___x_3592_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_3582_);
lean_dec(v_id_3581_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3594_, lean_object* v_expectedType_x3f_3595_, lean_object* v_as_x27_3596_, lean_object* v_b_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3594_, v_expectedType_x3f_3595_, v_as_x27_3596_, v_b_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v_as_x27_3596_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3602_, lean_object* v_expectedType_x3f_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3607_; 
lean_inc(v_id_3602_);
v___x_3607_ = l_Lean_realizeGlobalConst(v_id_3602_, v_a_3604_, v_a_3605_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3636_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3636_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3636_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v_infoState_3613_; uint8_t v_enabled_3614_; 
v___x_3612_ = lean_st_ref_get(v_a_3605_);
v_infoState_3613_ = lean_ctor_get(v___x_3612_, 7);
lean_inc_ref(v_infoState_3613_);
lean_dec(v___x_3612_);
v_enabled_3614_ = lean_ctor_get_uint8(v_infoState_3613_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3613_);
if (v_enabled_3614_ == 0)
{
lean_object* v___x_3616_; 
lean_dec(v_expectedType_x3f_3603_);
lean_dec(v_id_3602_);
if (v_isShared_3611_ == 0)
{
v___x_3616_ = v___x_3610_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3608_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3610_);
v___x_3618_ = lean_box(0);
v___x_3619_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3602_, v_expectedType_x3f_3603_, v_a_3608_, v___x_3618_, v_a_3604_, v_a_3605_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3619_, 0);
lean_dec(v_unused_3627_);
v___x_3621_ = v___x_3619_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3619_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v_a_3608_);
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3608_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_a_3608_);
v_a_3628_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3619_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3619_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_3603_);
lean_dec(v_id_3602_);
return v___x_3607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3637_, lean_object* v_expectedType_x3f_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3637_, v_expectedType_x3f_3638_, v_a_3639_, v_a_3640_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3643_, lean_object* v_expectedType_x3f_3644_, lean_object* v_as_3645_, lean_object* v_as_x27_3646_, lean_object* v_b_3647_, lean_object* v_a_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3643_, v_expectedType_x3f_3644_, v_as_x27_3646_, v_b_3647_, v___y_3649_, v___y_3650_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3653_, lean_object* v_expectedType_x3f_3654_, lean_object* v_as_3655_, lean_object* v_as_x27_3656_, lean_object* v_b_3657_, lean_object* v_a_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3653_, v_expectedType_x3f_3654_, v_as_3655_, v_as_x27_3656_, v_b_3657_, v_a_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v_as_x27_3656_);
lean_dec(v_as_3655_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3663_, lean_object* v_as_x27_3664_, lean_object* v_b_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
if (lean_obj_tag(v_as_x27_3664_) == 0)
{
lean_object* v___x_3669_; 
lean_dec(v_ref_3663_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v_b_3665_);
return v___x_3669_;
}
else
{
lean_object* v_head_3670_; lean_object* v_tail_3671_; lean_object* v_fst_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_head_3670_ = lean_ctor_get(v_as_x27_3664_, 0);
v_tail_3671_ = lean_ctor_get(v_as_x27_3664_, 1);
v_fst_3672_ = lean_ctor_get(v_head_3670_, 0);
v___x_3673_ = lean_box(0);
lean_inc(v_fst_3672_);
lean_inc(v_ref_3663_);
v___x_3674_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3663_, v_fst_3672_, v___x_3673_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v___x_3675_; 
lean_dec_ref(v___x_3674_);
v___x_3675_ = lean_box(0);
v_as_x27_3664_ = v_tail_3671_;
v_b_3665_ = v___x_3675_;
goto _start;
}
else
{
lean_dec(v_ref_3663_);
return v___x_3674_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3677_, lean_object* v_as_x27_3678_, lean_object* v_b_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3677_, v_as_x27_3678_, v_b_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v_as_x27_3678_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3684_, lean_object* v_id_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_realizeGlobalName(v_id_3685_, v_a_3686_, v_a_3687_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3718_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3718_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3718_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v_infoState_3695_; uint8_t v_enabled_3696_; 
v___x_3694_ = lean_st_ref_get(v_a_3687_);
v_infoState_3695_ = lean_ctor_get(v___x_3694_, 7);
lean_inc_ref(v_infoState_3695_);
lean_dec(v___x_3694_);
v_enabled_3696_ = lean_ctor_get_uint8(v_infoState_3695_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3695_);
if (v_enabled_3696_ == 0)
{
lean_object* v___x_3698_; 
lean_dec(v_ref_3684_);
if (v_isShared_3693_ == 0)
{
v___x_3698_ = v___x_3692_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3690_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_del_object(v___x_3692_);
v___x_3700_ = lean_box(0);
v___x_3701_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3684_, v_a_3690_, v___x_3700_, v_a_3686_, v_a_3687_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v___x_3701_, 0);
lean_dec(v_unused_3709_);
v___x_3703_ = v___x_3701_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_dec(v___x_3701_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_a_3690_);
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3690_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_a_3690_);
v_a_3710_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3701_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3701_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_3684_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3719_, lean_object* v_id_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3719_, v_id_3720_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3725_, lean_object* v_as_3726_, lean_object* v_as_x27_3727_, lean_object* v_b_3728_, lean_object* v_a_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3725_, v_as_x27_3727_, v_b_3728_, v___y_3730_, v___y_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3734_, lean_object* v_as_3735_, lean_object* v_as_x27_3736_, lean_object* v_b_3737_, lean_object* v_a_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3734_, v_as_3735_, v_as_x27_3736_, v_b_3737_, v_a_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v_as_x27_3736_);
lean_dec(v_as_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3743_){
_start:
{
lean_object* v_fst_3744_; 
v_fst_3744_ = lean_ctor_get(v_self_3743_, 0);
lean_inc(v_fst_3744_);
return v_fst_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3745_);
lean_dec_ref(v_self_3745_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3747_, lean_object* v_treesSaved_3748_, lean_object* v_s_3749_){
_start:
{
if (lean_obj_tag(v_info_3747_) == 0)
{
uint8_t v_enabled_3750_; lean_object* v_assignment_3751_; lean_object* v_lazyAssignment_3752_; lean_object* v_trees_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3763_; 
v_enabled_3750_ = lean_ctor_get_uint8(v_s_3749_, sizeof(void*)*3);
v_assignment_3751_ = lean_ctor_get(v_s_3749_, 0);
v_lazyAssignment_3752_ = lean_ctor_get(v_s_3749_, 1);
v_trees_3753_ = lean_ctor_get(v_s_3749_, 2);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_s_3749_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3755_ = v_s_3749_;
v_isShared_3756_ = v_isSharedCheck_3763_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_trees_3753_);
lean_inc(v_lazyAssignment_3752_);
lean_inc(v_assignment_3751_);
lean_dec(v_s_3749_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3763_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_val_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
v_val_3757_ = lean_ctor_get(v_info_3747_, 0);
lean_inc(v_val_3757_);
lean_dec_ref(v_info_3747_);
v___x_3758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3758_, 0, v_val_3757_);
lean_ctor_set(v___x_3758_, 1, v_trees_3753_);
v___x_3759_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3748_, v___x_3758_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 2, v___x_3759_);
v___x_3761_ = v___x_3755_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_assignment_3751_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_lazyAssignment_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v___x_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*3, v_enabled_3750_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
else
{
uint8_t v_enabled_3764_; lean_object* v_assignment_3765_; lean_object* v_lazyAssignment_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3782_; 
v_enabled_3764_ = lean_ctor_get_uint8(v_s_3749_, sizeof(void*)*3);
v_assignment_3765_ = lean_ctor_get(v_s_3749_, 0);
v_lazyAssignment_3766_ = lean_ctor_get(v_s_3749_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_s_3749_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v_s_3749_, 2);
lean_dec(v_unused_3783_);
v___x_3768_ = v_s_3749_;
v_isShared_3769_ = v_isSharedCheck_3782_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_lazyAssignment_3766_);
lean_inc(v_assignment_3765_);
lean_dec(v_s_3749_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3782_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v_val_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3781_; 
v_val_3770_ = lean_ctor_get(v_info_3747_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_info_3747_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3772_ = v_info_3747_;
v_isShared_3773_ = v_isSharedCheck_3781_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_val_3770_);
lean_dec(v_info_3747_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3781_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 2);
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_val_3770_);
v___x_3775_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3776_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3748_, v___x_3775_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 2, v___x_3776_);
v___x_3778_ = v___x_3768_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_assignment_3765_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_lazyAssignment_3766_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v___x_3776_);
lean_ctor_set_uint8(v_reuseFailAlloc_3779_, sizeof(void*)*3, v_enabled_3764_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3784_, lean_object* v_modifyInfoState_3785_, lean_object* v_info_3786_){
_start:
{
lean_object* v___f_3787_; lean_object* v___x_3788_; 
v___f_3787_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3787_, 0, v_info_3786_);
lean_closure_set(v___f_3787_, 1, v_treesSaved_3784_);
v___x_3788_ = lean_apply_1(v_modifyInfoState_3785_, v___f_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3789_, lean_object* v_info_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_apply_1(v___f_3789_, v_info_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3792_, lean_object* v_toBind_3793_, lean_object* v___f_3794_, lean_object* v_____do__lift_3795_){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_____do__lift_3795_);
v___x_3797_ = lean_apply_2(v_toPure_3792_, lean_box(0), v___x_3796_);
v___x_3798_ = lean_apply_4(v_toBind_3793_, lean_box(0), lean_box(0), v___x_3797_, v___f_3794_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3799_, lean_object* v_mkInfoOnError_3800_, lean_object* v___f_3801_, lean_object* v_mkInfo_3802_, lean_object* v___f_3803_, lean_object* v_a_x3f_3804_){
_start:
{
if (lean_obj_tag(v_a_x3f_3804_) == 0)
{
lean_object* v___x_3805_; 
lean_dec(v___f_3803_);
lean_dec(v_mkInfo_3802_);
v___x_3805_ = lean_apply_4(v_toBind_3799_, lean_box(0), lean_box(0), v_mkInfoOnError_3800_, v___f_3801_);
return v___x_3805_;
}
else
{
lean_object* v_val_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_dec(v___f_3801_);
lean_dec(v_mkInfoOnError_3800_);
v_val_3806_ = lean_ctor_get(v_a_x3f_3804_, 0);
lean_inc(v_val_3806_);
lean_dec_ref(v_a_x3f_3804_);
v___x_3807_ = lean_apply_1(v_mkInfo_3802_, v_val_3806_);
v___x_3808_ = lean_apply_4(v_toBind_3799_, lean_box(0), lean_box(0), v___x_3807_, v___f_3803_);
return v___x_3808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3809_, lean_object* v_modifyInfoState_3810_, lean_object* v_toBind_3811_, lean_object* v_mkInfoOnError_3812_, lean_object* v_mkInfo_3813_, lean_object* v_inst_3814_, lean_object* v_x_3815_, lean_object* v___f_3816_, lean_object* v_treesSaved_3817_){
_start:
{
lean_object* v_toFunctor_3818_; lean_object* v_toPure_3819_; lean_object* v_map_3820_; lean_object* v___f_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_toFunctor_3818_ = lean_ctor_get(v_toApplicative_3809_, 0);
lean_inc_ref(v_toFunctor_3818_);
v_toPure_3819_ = lean_ctor_get(v_toApplicative_3809_, 1);
lean_inc(v_toPure_3819_);
lean_dec_ref(v_toApplicative_3809_);
v_map_3820_ = lean_ctor_get(v_toFunctor_3818_, 0);
lean_inc(v_map_3820_);
lean_dec_ref(v_toFunctor_3818_);
v___f_3821_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3821_, 0, v_treesSaved_3817_);
lean_closure_set(v___f_3821_, 1, v_modifyInfoState_3810_);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3822_, 0, v___f_3821_);
lean_inc_ref(v___f_3822_);
lean_inc(v_toBind_3811_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3823_, 0, v_toPure_3819_);
lean_closure_set(v___f_3823_, 1, v_toBind_3811_);
lean_closure_set(v___f_3823_, 2, v___f_3822_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3824_, 0, v_toBind_3811_);
lean_closure_set(v___f_3824_, 1, v_mkInfoOnError_3812_);
lean_closure_set(v___f_3824_, 2, v___f_3823_);
lean_closure_set(v___f_3824_, 3, v_mkInfo_3813_);
lean_closure_set(v___f_3824_, 4, v___f_3822_);
v___x_3825_ = lean_apply_4(v_inst_3814_, lean_box(0), lean_box(0), v_x_3815_, v___f_3824_);
v___x_3826_ = lean_apply_4(v_map_3820_, lean_box(0), lean_box(0), v___f_3816_, v___x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3827_, lean_object* v_inst_3828_, lean_object* v_inst_3829_, lean_object* v_toBind_3830_, lean_object* v___f_3831_, lean_object* v_____do__lift_3832_){
_start:
{
uint8_t v_enabled_3833_; 
v_enabled_3833_ = lean_ctor_get_uint8(v_____do__lift_3832_, sizeof(void*)*3);
if (v_enabled_3833_ == 0)
{
lean_dec(v___f_3831_);
lean_dec(v_toBind_3830_);
lean_dec_ref(v_inst_3829_);
lean_dec_ref(v_inst_3828_);
lean_inc(v_x_3827_);
return v_x_3827_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3828_, v_inst_3829_);
v___x_3835_ = lean_apply_4(v_toBind_3830_, lean_box(0), lean_box(0), v___x_3834_, v___f_3831_);
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3836_, lean_object* v_inst_3837_, lean_object* v_inst_3838_, lean_object* v_toBind_3839_, lean_object* v___f_3840_, lean_object* v_____do__lift_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3836_, v_inst_3837_, v_inst_3838_, v_toBind_3839_, v___f_3840_, v_____do__lift_3841_);
lean_dec_ref(v_____do__lift_3841_);
lean_dec(v_x_3836_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3844_, lean_object* v_inst_3845_, lean_object* v_inst_3846_, lean_object* v_x_3847_, lean_object* v_mkInfo_3848_, lean_object* v_mkInfoOnError_3849_){
_start:
{
lean_object* v_toApplicative_3850_; lean_object* v_toBind_3851_; lean_object* v_getInfoState_3852_; lean_object* v_modifyInfoState_3853_; lean_object* v___f_3854_; lean_object* v___f_3855_; lean_object* v___f_3856_; lean_object* v___x_3857_; 
v_toApplicative_3850_ = lean_ctor_get(v_inst_3844_, 0);
v_toBind_3851_ = lean_ctor_get(v_inst_3844_, 1);
lean_inc_n(v_toBind_3851_, 3);
v_getInfoState_3852_ = lean_ctor_get(v_inst_3845_, 0);
lean_inc(v_getInfoState_3852_);
v_modifyInfoState_3853_ = lean_ctor_get(v_inst_3845_, 1);
v___f_3854_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3847_);
lean_inc(v_modifyInfoState_3853_);
lean_inc_ref(v_toApplicative_3850_);
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3855_, 0, v_toApplicative_3850_);
lean_closure_set(v___f_3855_, 1, v_modifyInfoState_3853_);
lean_closure_set(v___f_3855_, 2, v_toBind_3851_);
lean_closure_set(v___f_3855_, 3, v_mkInfoOnError_3849_);
lean_closure_set(v___f_3855_, 4, v_mkInfo_3848_);
lean_closure_set(v___f_3855_, 5, v_inst_3846_);
lean_closure_set(v___f_3855_, 6, v_x_3847_);
lean_closure_set(v___f_3855_, 7, v___f_3854_);
v___f_3856_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3856_, 0, v_x_3847_);
lean_closure_set(v___f_3856_, 1, v_inst_3844_);
lean_closure_set(v___f_3856_, 2, v_inst_3845_);
lean_closure_set(v___f_3856_, 3, v_toBind_3851_);
lean_closure_set(v___f_3856_, 4, v___f_3855_);
v___x_3857_ = lean_apply_4(v_toBind_3851_, lean_box(0), lean_box(0), v_getInfoState_3852_, v___f_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3858_, lean_object* v_inst_3859_, lean_object* v_inst_3860_, lean_object* v_00_u03b1_3861_, lean_object* v_inst_3862_, lean_object* v_x_3863_, lean_object* v_mkInfo_3864_, lean_object* v_mkInfoOnError_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3859_, v_inst_3860_, v_inst_3862_, v_x_3863_, v_mkInfo_3864_, v_mkInfoOnError_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3867_, lean_object* v_tree_3868_, lean_object* v_s_3869_){
_start:
{
uint8_t v_enabled_3870_; lean_object* v_assignment_3871_; lean_object* v_lazyAssignment_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3880_; 
v_enabled_3870_ = lean_ctor_get_uint8(v_s_3869_, sizeof(void*)*3);
v_assignment_3871_ = lean_ctor_get(v_s_3869_, 0);
v_lazyAssignment_3872_ = lean_ctor_get(v_s_3869_, 1);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_s_3869_);
if (v_isSharedCheck_3880_ == 0)
{
lean_object* v_unused_3881_; 
v_unused_3881_ = lean_ctor_get(v_s_3869_, 2);
lean_dec(v_unused_3881_);
v___x_3874_ = v_s_3869_;
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_lazyAssignment_3872_);
lean_inc(v_assignment_3871_);
lean_dec(v_s_3869_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3867_, v_tree_3868_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 2, v___x_3876_);
v___x_3878_ = v___x_3874_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_assignment_3871_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_lazyAssignment_3872_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v___x_3876_);
lean_ctor_set_uint8(v_reuseFailAlloc_3879_, sizeof(void*)*3, v_enabled_3870_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3882_, lean_object* v_modifyInfoState_3883_, lean_object* v_tree_3884_){
_start:
{
lean_object* v___f_3885_; lean_object* v___x_3886_; 
v___f_3885_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3885_, 0, v_treesSaved_3882_);
lean_closure_set(v___f_3885_, 1, v_tree_3884_);
v___x_3886_ = lean_apply_1(v_modifyInfoState_3883_, v___f_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3887_, lean_object* v_toBind_3888_, lean_object* v___f_3889_, lean_object* v_st_3890_){
_start:
{
lean_object* v_trees_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_trees_3891_ = lean_ctor_get(v_st_3890_, 2);
lean_inc_ref(v_trees_3891_);
lean_dec_ref(v_st_3890_);
v___x_3892_ = lean_apply_1(v_mkInfoTree_3887_, v_trees_3891_);
v___x_3893_ = lean_apply_4(v_toBind_3888_, lean_box(0), lean_box(0), v___x_3892_, v___f_3889_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3894_, lean_object* v_getInfoState_3895_, lean_object* v___f_3896_, lean_object* v_x_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_apply_4(v_toBind_3894_, lean_box(0), lean_box(0), v_getInfoState_3895_, v___f_3896_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3899_, lean_object* v_getInfoState_3900_, lean_object* v___f_3901_, lean_object* v_x_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3899_, v_getInfoState_3900_, v___f_3901_, v_x_3902_);
lean_dec(v_x_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3904_, lean_object* v_modifyInfoState_3905_, lean_object* v_mkInfoTree_3906_, lean_object* v_toBind_3907_, lean_object* v_getInfoState_3908_, lean_object* v_inst_3909_, lean_object* v_x_3910_, lean_object* v___f_3911_, lean_object* v_treesSaved_3912_){
_start:
{
lean_object* v_toFunctor_3913_; lean_object* v_map_3914_; lean_object* v___f_3915_; lean_object* v___f_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_toFunctor_3913_ = lean_ctor_get(v_toApplicative_3904_, 0);
lean_inc_ref(v_toFunctor_3913_);
lean_dec_ref(v_toApplicative_3904_);
v_map_3914_ = lean_ctor_get(v_toFunctor_3913_, 0);
lean_inc(v_map_3914_);
lean_dec_ref(v_toFunctor_3913_);
v___f_3915_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3915_, 0, v_treesSaved_3912_);
lean_closure_set(v___f_3915_, 1, v_modifyInfoState_3905_);
lean_inc(v_toBind_3907_);
v___f_3916_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3916_, 0, v_mkInfoTree_3906_);
lean_closure_set(v___f_3916_, 1, v_toBind_3907_);
lean_closure_set(v___f_3916_, 2, v___f_3915_);
v___f_3917_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3917_, 0, v_toBind_3907_);
lean_closure_set(v___f_3917_, 1, v_getInfoState_3908_);
lean_closure_set(v___f_3917_, 2, v___f_3916_);
v___x_3918_ = lean_apply_4(v_inst_3909_, lean_box(0), lean_box(0), v_x_3910_, v___f_3917_);
v___x_3919_ = lean_apply_4(v_map_3914_, lean_box(0), lean_box(0), v___f_3911_, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3920_, lean_object* v_inst_3921_, lean_object* v_inst_3922_, lean_object* v_x_3923_, lean_object* v_mkInfoTree_3924_){
_start:
{
lean_object* v_toApplicative_3925_; lean_object* v_toBind_3926_; lean_object* v_getInfoState_3927_; lean_object* v_modifyInfoState_3928_; lean_object* v___f_3929_; lean_object* v___f_3930_; lean_object* v___f_3931_; lean_object* v___x_3932_; 
v_toApplicative_3925_ = lean_ctor_get(v_inst_3920_, 0);
v_toBind_3926_ = lean_ctor_get(v_inst_3920_, 1);
lean_inc_n(v_toBind_3926_, 3);
v_getInfoState_3927_ = lean_ctor_get(v_inst_3921_, 0);
lean_inc_n(v_getInfoState_3927_, 2);
v_modifyInfoState_3928_ = lean_ctor_get(v_inst_3921_, 1);
v___f_3929_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3923_);
lean_inc(v_modifyInfoState_3928_);
lean_inc_ref(v_toApplicative_3925_);
v___f_3930_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3930_, 0, v_toApplicative_3925_);
lean_closure_set(v___f_3930_, 1, v_modifyInfoState_3928_);
lean_closure_set(v___f_3930_, 2, v_mkInfoTree_3924_);
lean_closure_set(v___f_3930_, 3, v_toBind_3926_);
lean_closure_set(v___f_3930_, 4, v_getInfoState_3927_);
lean_closure_set(v___f_3930_, 5, v_inst_3922_);
lean_closure_set(v___f_3930_, 6, v_x_3923_);
lean_closure_set(v___f_3930_, 7, v___f_3929_);
v___f_3931_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3931_, 0, v_x_3923_);
lean_closure_set(v___f_3931_, 1, v_inst_3920_);
lean_closure_set(v___f_3931_, 2, v_inst_3921_);
lean_closure_set(v___f_3931_, 3, v_toBind_3926_);
lean_closure_set(v___f_3931_, 4, v___f_3930_);
v___x_3932_ = lean_apply_4(v_toBind_3926_, lean_box(0), lean_box(0), v_getInfoState_3927_, v___f_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3933_, lean_object* v_inst_3934_, lean_object* v_inst_3935_, lean_object* v_00_u03b1_3936_, lean_object* v_inst_3937_, lean_object* v_x_3938_, lean_object* v_mkInfoTree_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3934_, v_inst_3935_, v_inst_3937_, v_x_3938_, v_mkInfoTree_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3941_, lean_object* v_toPure_3942_, lean_object* v_____do__lift_3943_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3944_, 0, v_____do__lift_3943_);
lean_ctor_set(v___x_3944_, 1, v_trees_3941_);
v___x_3945_ = lean_apply_2(v_toPure_3942_, lean_box(0), v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3946_, lean_object* v_toBind_3947_, lean_object* v_mkInfo_3948_, lean_object* v_trees_3949_){
_start:
{
lean_object* v___f_3950_; lean_object* v___x_3951_; 
v___f_3950_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3950_, 0, v_trees_3949_);
lean_closure_set(v___f_3950_, 1, v_toPure_3946_);
v___x_3951_ = lean_apply_4(v_toBind_3947_, lean_box(0), lean_box(0), v_mkInfo_3948_, v___f_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3952_, lean_object* v_inst_3953_, lean_object* v_inst_3954_, lean_object* v_x_3955_, lean_object* v_mkInfo_3956_){
_start:
{
lean_object* v_toApplicative_3957_; lean_object* v_toBind_3958_; lean_object* v_toPure_3959_; lean_object* v___f_3960_; lean_object* v___x_3961_; 
v_toApplicative_3957_ = lean_ctor_get(v_inst_3952_, 0);
v_toBind_3958_ = lean_ctor_get(v_inst_3952_, 1);
v_toPure_3959_ = lean_ctor_get(v_toApplicative_3957_, 1);
lean_inc(v_toBind_3958_);
lean_inc(v_toPure_3959_);
v___f_3960_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3960_, 0, v_toPure_3959_);
lean_closure_set(v___f_3960_, 1, v_toBind_3958_);
lean_closure_set(v___f_3960_, 2, v_mkInfo_3956_);
v___x_3961_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3952_, v_inst_3953_, v_inst_3954_, v_x_3955_, v___f_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3962_, lean_object* v_inst_3963_, lean_object* v_inst_3964_, lean_object* v_00_u03b1_3965_, lean_object* v_inst_3966_, lean_object* v_x_3967_, lean_object* v_mkInfo_3968_){
_start:
{
lean_object* v_toApplicative_3969_; lean_object* v_toBind_3970_; lean_object* v_toPure_3971_; lean_object* v___f_3972_; lean_object* v___x_3973_; 
v_toApplicative_3969_ = lean_ctor_get(v_inst_3963_, 0);
v_toBind_3970_ = lean_ctor_get(v_inst_3963_, 1);
v_toPure_3971_ = lean_ctor_get(v_toApplicative_3969_, 1);
lean_inc(v_toBind_3970_);
lean_inc(v_toPure_3971_);
v___f_3972_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3972_, 0, v_toPure_3971_);
lean_closure_set(v___f_3972_, 1, v_toBind_3970_);
lean_closure_set(v___f_3972_, 2, v_mkInfo_3968_);
v___x_3973_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3963_, v_inst_3964_, v_inst_3966_, v_x_3967_, v___f_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3974_, lean_object* v_trees_3975_, lean_object* v_s_3976_){
_start:
{
uint8_t v_enabled_3977_; lean_object* v_assignment_3978_; lean_object* v_lazyAssignment_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3987_; 
v_enabled_3977_ = lean_ctor_get_uint8(v_s_3976_, sizeof(void*)*3);
v_assignment_3978_ = lean_ctor_get(v_s_3976_, 0);
v_lazyAssignment_3979_ = lean_ctor_get(v_s_3976_, 1);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_s_3976_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v_s_3976_, 2);
lean_dec(v_unused_3988_);
v___x_3981_ = v_s_3976_;
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_lazyAssignment_3979_);
lean_inc(v_assignment_3978_);
lean_dec(v_s_3976_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3974_, v_trees_3975_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 2, v___x_3983_);
v___x_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_assignment_3978_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_lazyAssignment_3979_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v___x_3983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3986_, sizeof(void*)*3, v_enabled_3977_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3989_, lean_object* v_trees_3990_, lean_object* v_s_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3989_, v_trees_3990_, v_s_3991_);
lean_dec_ref(v_trees_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3993_, lean_object* v_modifyInfoState_3994_, lean_object* v_trees_3995_){
_start:
{
lean_object* v___f_3996_; lean_object* v___x_3997_; 
v___f_3996_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3996_, 0, v_treesSaved_3993_);
lean_closure_set(v___f_3996_, 1, v_trees_3995_);
v___x_3997_ = lean_apply_1(v_modifyInfoState_3994_, v___f_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3998_, lean_object* v_tree_3999_, lean_object* v_____do__lift_4000_){
_start:
{
if (lean_obj_tag(v_____do__lift_4000_) == 0)
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_apply_2(v_toPure_3998_, lean_box(0), v_tree_3999_);
return v___x_4001_;
}
else
{
lean_object* v_val_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_val_4002_ = lean_ctor_get(v_____do__lift_4000_, 0);
lean_inc(v_val_4002_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v_val_4002_);
lean_ctor_set(v___x_4003_, 1, v_tree_3999_);
v___x_4004_ = lean_apply_2(v_toPure_3998_, lean_box(0), v___x_4003_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_4005_, lean_object* v_tree_4006_, lean_object* v_____do__lift_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_4005_, v_tree_4006_, v_____do__lift_4007_);
lean_dec(v_____do__lift_4007_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4009_, lean_object* v_toPure_4010_, lean_object* v_toBind_4011_, lean_object* v_ctx_x3f_4012_, lean_object* v_tree_4013_){
_start:
{
lean_object* v_tree_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; 
v_tree_4014_ = l_Lean_Elab_InfoTree_substitute(v_tree_4013_, v_assignment_4009_);
v___f_4015_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4015_, 0, v_toPure_4010_);
lean_closure_set(v___f_4015_, 1, v_tree_4014_);
v___x_4016_ = lean_apply_4(v_toBind_4011_, lean_box(0), lean_box(0), v_ctx_x3f_4012_, v___f_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_4017_, lean_object* v_toPure_4018_, lean_object* v_toBind_4019_, lean_object* v_ctx_x3f_4020_, lean_object* v_tree_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_4017_, v_toPure_4018_, v_toBind_4019_, v_ctx_x3f_4020_, v_tree_4021_);
lean_dec_ref(v_assignment_4017_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4023_, lean_object* v_toBind_4024_, lean_object* v_ctx_x3f_4025_, lean_object* v_inst_4026_, lean_object* v___f_4027_, lean_object* v_st_4028_){
_start:
{
lean_object* v_assignment_4029_; lean_object* v_trees_4030_; lean_object* v___f_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v_assignment_4029_ = lean_ctor_get(v_st_4028_, 0);
lean_inc_ref(v_assignment_4029_);
v_trees_4030_ = lean_ctor_get(v_st_4028_, 2);
lean_inc_ref(v_trees_4030_);
lean_dec_ref(v_st_4028_);
lean_inc(v_toBind_4024_);
v___f_4031_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4031_, 0, v_assignment_4029_);
lean_closure_set(v___f_4031_, 1, v_toPure_4023_);
lean_closure_set(v___f_4031_, 2, v_toBind_4024_);
lean_closure_set(v___f_4031_, 3, v_ctx_x3f_4025_);
v___x_4032_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4026_, v___f_4031_, v_trees_4030_);
v___x_4033_ = lean_apply_4(v_toBind_4024_, lean_box(0), lean_box(0), v___x_4032_, v___f_4027_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4034_, lean_object* v_modifyInfoState_4035_, lean_object* v_toBind_4036_, lean_object* v_ctx_x3f_4037_, lean_object* v_inst_4038_, lean_object* v_getInfoState_4039_, lean_object* v_inst_4040_, lean_object* v_x_4041_, lean_object* v___f_4042_, lean_object* v_treesSaved_4043_){
_start:
{
lean_object* v_toFunctor_4044_; lean_object* v_toPure_4045_; lean_object* v_map_4046_; lean_object* v___f_4047_; lean_object* v___f_4048_; lean_object* v___f_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_toFunctor_4044_ = lean_ctor_get(v_toApplicative_4034_, 0);
lean_inc_ref(v_toFunctor_4044_);
v_toPure_4045_ = lean_ctor_get(v_toApplicative_4034_, 1);
lean_inc(v_toPure_4045_);
lean_dec_ref(v_toApplicative_4034_);
v_map_4046_ = lean_ctor_get(v_toFunctor_4044_, 0);
lean_inc(v_map_4046_);
lean_dec_ref(v_toFunctor_4044_);
v___f_4047_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4047_, 0, v_treesSaved_4043_);
lean_closure_set(v___f_4047_, 1, v_modifyInfoState_4035_);
lean_inc(v_toBind_4036_);
v___f_4048_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4048_, 0, v_toPure_4045_);
lean_closure_set(v___f_4048_, 1, v_toBind_4036_);
lean_closure_set(v___f_4048_, 2, v_ctx_x3f_4037_);
lean_closure_set(v___f_4048_, 3, v_inst_4038_);
lean_closure_set(v___f_4048_, 4, v___f_4047_);
v___f_4049_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4049_, 0, v_toBind_4036_);
lean_closure_set(v___f_4049_, 1, v_getInfoState_4039_);
lean_closure_set(v___f_4049_, 2, v___f_4048_);
v___x_4050_ = lean_apply_4(v_inst_4040_, lean_box(0), lean_box(0), v_x_4041_, v___f_4049_);
v___x_4051_ = lean_apply_4(v_map_4046_, lean_box(0), lean_box(0), v___f_4042_, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_inst_4054_, lean_object* v_x_4055_, lean_object* v_ctx_x3f_4056_){
_start:
{
lean_object* v_toApplicative_4057_; lean_object* v_toBind_4058_; lean_object* v_getInfoState_4059_; lean_object* v_modifyInfoState_4060_; lean_object* v___f_4061_; lean_object* v___f_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; 
v_toApplicative_4057_ = lean_ctor_get(v_inst_4052_, 0);
v_toBind_4058_ = lean_ctor_get(v_inst_4052_, 1);
lean_inc_n(v_toBind_4058_, 3);
v_getInfoState_4059_ = lean_ctor_get(v_inst_4053_, 0);
lean_inc_n(v_getInfoState_4059_, 2);
v_modifyInfoState_4060_ = lean_ctor_get(v_inst_4053_, 1);
v___f_4061_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4055_);
lean_inc_ref(v_inst_4052_);
lean_inc(v_modifyInfoState_4060_);
lean_inc_ref(v_toApplicative_4057_);
v___f_4062_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4062_, 0, v_toApplicative_4057_);
lean_closure_set(v___f_4062_, 1, v_modifyInfoState_4060_);
lean_closure_set(v___f_4062_, 2, v_toBind_4058_);
lean_closure_set(v___f_4062_, 3, v_ctx_x3f_4056_);
lean_closure_set(v___f_4062_, 4, v_inst_4052_);
lean_closure_set(v___f_4062_, 5, v_getInfoState_4059_);
lean_closure_set(v___f_4062_, 6, v_inst_4054_);
lean_closure_set(v___f_4062_, 7, v_x_4055_);
lean_closure_set(v___f_4062_, 8, v___f_4061_);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4063_, 0, v_x_4055_);
lean_closure_set(v___f_4063_, 1, v_inst_4052_);
lean_closure_set(v___f_4063_, 2, v_inst_4053_);
lean_closure_set(v___f_4063_, 3, v_toBind_4058_);
lean_closure_set(v___f_4063_, 4, v___f_4062_);
v___x_4064_ = lean_apply_4(v_toBind_4058_, lean_box(0), lean_box(0), v_getInfoState_4059_, v___f_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4065_, lean_object* v_inst_4066_, lean_object* v_inst_4067_, lean_object* v_00_u03b1_4068_, lean_object* v_inst_4069_, lean_object* v_x_4070_, lean_object* v_ctx_x3f_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4066_, v_inst_4067_, v_inst_4069_, v_x_4070_, v_ctx_x3f_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4073_, lean_object* v_____do__lift_4074_){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_____do__lift_4074_);
v___x_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
v___x_4077_ = lean_apply_2(v_toPure_4073_, lean_box(0), v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4078_, lean_object* v_inst_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_inst_4084_, lean_object* v_inst_4085_, lean_object* v_inst_4086_, lean_object* v_x_4087_){
_start:
{
lean_object* v_toApplicative_4088_; lean_object* v_toBind_4089_; lean_object* v_toPure_4090_; lean_object* v___x_4091_; lean_object* v___f_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_toApplicative_4088_ = lean_ctor_get(v_inst_4078_, 0);
v_toBind_4089_ = lean_ctor_get(v_inst_4078_, 1);
v_toPure_4090_ = lean_ctor_get(v_toApplicative_4088_, 1);
lean_inc_ref(v_inst_4078_);
v___x_4091_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4078_, v_inst_4082_, v_inst_4084_, v_inst_4083_, v_inst_4085_, v_inst_4080_, v_inst_4086_);
lean_inc(v_toPure_4090_);
v___f_4092_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4092_, 0, v_toPure_4090_);
lean_inc(v_toBind_4089_);
v___x_4093_ = lean_apply_4(v_toBind_4089_, lean_box(0), lean_box(0), v___x_4091_, v___f_4092_);
v___x_4094_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4078_, v_inst_4079_, v_inst_4081_, v_x_4087_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4095_, lean_object* v_inst_4096_, lean_object* v_inst_4097_, lean_object* v_00_u03b1_4098_, lean_object* v_inst_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_inst_4104_, lean_object* v_inst_4105_, lean_object* v_x_4106_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4096_, v_inst_4097_, v_inst_4099_, v_inst_4100_, v_inst_4101_, v_inst_4102_, v_inst_4103_, v_inst_4104_, v_inst_4105_, v_x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4108_, lean_object* v_____x_4109_){
_start:
{
if (lean_obj_tag(v_____x_4109_) == 1)
{
lean_object* v_val_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4119_; 
v_val_4110_ = lean_ctor_get(v_____x_4109_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_____x_4109_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4112_ = v_____x_4109_;
v_isShared_4113_ = v_isSharedCheck_4119_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_val_4110_);
lean_dec(v_____x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4119_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_val_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v___x_4114_);
v___x_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_apply_2(v_toPure_4108_, lean_box(0), v___x_4116_);
return v___x_4117_;
}
}
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v_____x_4109_);
v___x_4120_ = lean_box(0);
v___x_4121_ = lean_apply_2(v_toPure_4108_, lean_box(0), v___x_4120_);
return v___x_4121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4122_, lean_object* v_inst_4123_, lean_object* v_inst_4124_, lean_object* v_inst_4125_, lean_object* v_x_4126_){
_start:
{
lean_object* v_toApplicative_4127_; lean_object* v_toBind_4128_; lean_object* v_toPure_4129_; lean_object* v___f_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_toApplicative_4127_ = lean_ctor_get(v_inst_4122_, 0);
v_toBind_4128_ = lean_ctor_get(v_inst_4122_, 1);
v_toPure_4129_ = lean_ctor_get(v_toApplicative_4127_, 1);
lean_inc(v_toPure_4129_);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4130_, 0, v_toPure_4129_);
lean_inc(v_toBind_4128_);
v___x_4131_ = lean_apply_4(v_toBind_4128_, lean_box(0), lean_box(0), v_inst_4125_, v___f_4130_);
v___x_4132_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4122_, v_inst_4123_, v_inst_4124_, v_x_4126_, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4133_, lean_object* v_inst_4134_, lean_object* v_inst_4135_, lean_object* v_00_u03b1_4136_, lean_object* v_inst_4137_, lean_object* v_inst_4138_, lean_object* v_x_4139_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4134_, v_inst_4135_, v_inst_4137_, v_inst_4138_, v_x_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4141_, lean_object* v_autoImplicits_4142_){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4143_, 0, v_autoImplicits_4142_);
v___x_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = lean_apply_2(v_toPure_4141_, lean_box(0), v___x_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4146_, lean_object* v_inst_4147_, lean_object* v_inst_4148_, lean_object* v_inst_4149_, lean_object* v_x_4150_){
_start:
{
lean_object* v_toApplicative_4151_; lean_object* v_toBind_4152_; lean_object* v_toPure_4153_; lean_object* v___f_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_toApplicative_4151_ = lean_ctor_get(v_inst_4146_, 0);
v_toBind_4152_ = lean_ctor_get(v_inst_4146_, 1);
v_toPure_4153_ = lean_ctor_get(v_toApplicative_4151_, 1);
lean_inc(v_toPure_4153_);
v___f_4154_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4154_, 0, v_toPure_4153_);
lean_inc(v_toBind_4152_);
v___x_4155_ = lean_apply_4(v_toBind_4152_, lean_box(0), lean_box(0), v_inst_4149_, v___f_4154_);
v___x_4156_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4146_, v_inst_4147_, v_inst_4148_, v_x_4150_, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4157_, lean_object* v_inst_4158_, lean_object* v_inst_4159_, lean_object* v_00_u03b1_4160_, lean_object* v_inst_4161_, lean_object* v_inst_4162_, lean_object* v_x_4163_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4158_, v_inst_4159_, v_inst_4161_, v_inst_4162_, v_x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v_mvarId_4167_, lean_object* v_toPure_4168_, lean_object* v_____do__lift_4169_){
_start:
{
lean_object* v_assignment_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_assignment_4170_ = lean_ctor_get(v_____do__lift_4169_, 0);
v___x_4171_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4165_, v___x_4166_, v_assignment_4170_, v_mvarId_4167_);
v___x_4172_ = lean_apply_2(v_toPure_4168_, lean_box(0), v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_4173_, lean_object* v___x_4174_, lean_object* v_mvarId_4175_, lean_object* v_toPure_4176_, lean_object* v_____do__lift_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_4173_, v___x_4174_, v_mvarId_4175_, v_toPure_4176_, v_____do__lift_4177_);
lean_dec_ref(v_____do__lift_4177_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_mvarId_4183_){
_start:
{
lean_object* v_toApplicative_4184_; lean_object* v_toBind_4185_; lean_object* v_getInfoState_4186_; lean_object* v_toPure_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___f_4190_; lean_object* v___x_4191_; 
v_toApplicative_4184_ = lean_ctor_get(v_inst_4181_, 0);
lean_inc_ref(v_toApplicative_4184_);
v_toBind_4185_ = lean_ctor_get(v_inst_4181_, 1);
lean_inc(v_toBind_4185_);
lean_dec_ref(v_inst_4181_);
v_getInfoState_4186_ = lean_ctor_get(v_inst_4182_, 0);
lean_inc(v_getInfoState_4186_);
lean_dec_ref(v_inst_4182_);
v_toPure_4187_ = lean_ctor_get(v_toApplicative_4184_, 1);
lean_inc(v_toPure_4187_);
lean_dec_ref(v_toApplicative_4184_);
v___x_4188_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4189_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4190_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4190_, 0, v___x_4188_);
lean_closure_set(v___f_4190_, 1, v___x_4189_);
lean_closure_set(v___f_4190_, 2, v_mvarId_4183_);
lean_closure_set(v___f_4190_, 3, v_toPure_4187_);
v___x_4191_ = lean_apply_4(v_toBind_4185_, lean_box(0), lean_box(0), v_getInfoState_4186_, v___f_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_mvarId_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4193_, v_inst_4194_, v_mvarId_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4197_, lean_object* v_infoTree_4198_, lean_object* v_s_4199_){
_start:
{
uint8_t v_enabled_4200_; lean_object* v_assignment_4201_; lean_object* v_lazyAssignment_4202_; lean_object* v_trees_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4213_; 
v_enabled_4200_ = lean_ctor_get_uint8(v_s_4199_, sizeof(void*)*3);
v_assignment_4201_ = lean_ctor_get(v_s_4199_, 0);
v_lazyAssignment_4202_ = lean_ctor_get(v_s_4199_, 1);
v_trees_4203_ = lean_ctor_get(v_s_4199_, 2);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_s_4199_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4205_ = v_s_4199_;
v_isShared_4206_ = v_isSharedCheck_4213_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_trees_4203_);
lean_inc(v_lazyAssignment_4202_);
lean_inc(v_assignment_4201_);
lean_dec(v_s_4199_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4213_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4207_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4208_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4209_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4207_, v___x_4208_, v_assignment_4201_, v_mvarId_4197_, v_infoTree_4198_);
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4209_);
v___x_4211_ = v___x_4205_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_lazyAssignment_4202_);
lean_ctor_set(v_reuseFailAlloc_4212_, 2, v_trees_4203_);
lean_ctor_set_uint8(v_reuseFailAlloc_4212_, sizeof(void*)*3, v_enabled_4200_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4216_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4217_ = lean_unsigned_to_nat(2u);
v___x_4218_ = lean_unsigned_to_nat(481u);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4220_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4221_ = l_mkPanicMessageWithDecl(v___x_4220_, v___x_4219_, v___x_4218_, v___x_4217_, v___x_4216_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4222_, lean_object* v___f_4223_, lean_object* v_inst_4224_, lean_object* v_____do__lift_4225_){
_start:
{
if (lean_obj_tag(v_____do__lift_4225_) == 0)
{
lean_object* v_modifyInfoState_4226_; lean_object* v___x_4227_; 
lean_dec_ref(v_inst_4224_);
v_modifyInfoState_4226_ = lean_ctor_get(v_inst_4222_, 1);
lean_inc(v_modifyInfoState_4226_);
lean_dec_ref(v_inst_4222_);
v___x_4227_ = lean_apply_1(v_modifyInfoState_4226_, v___f_4223_);
return v___x_4227_;
}
else
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec_ref(v___f_4223_);
lean_dec_ref(v_inst_4222_);
v___x_4228_ = lean_box(0);
v___x_4229_ = l_instInhabitedOfMonad___redArg(v_inst_4224_, v___x_4228_);
v___x_4230_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4231_ = l_panic___redArg(v___x_4229_, v___x_4230_);
lean_dec(v___x_4229_);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4232_, lean_object* v___f_4233_, lean_object* v_inst_4234_, lean_object* v_____do__lift_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4232_, v___f_4233_, v_inst_4234_, v_____do__lift_4235_);
lean_dec(v_____do__lift_4235_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4237_, lean_object* v_inst_4238_, lean_object* v_mvarId_4239_, lean_object* v_infoTree_4240_){
_start:
{
lean_object* v_toBind_4241_; lean_object* v___f_4242_; lean_object* v___f_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_toBind_4241_ = lean_ctor_get(v_inst_4237_, 1);
lean_inc(v_toBind_4241_);
lean_inc(v_mvarId_4239_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4242_, 0, v_mvarId_4239_);
lean_closure_set(v___f_4242_, 1, v_infoTree_4240_);
lean_inc_ref(v_inst_4237_);
lean_inc_ref(v_inst_4238_);
v___f_4243_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4243_, 0, v_inst_4238_);
lean_closure_set(v___f_4243_, 1, v___f_4242_);
lean_closure_set(v___f_4243_, 2, v_inst_4237_);
v___x_4244_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4237_, v_inst_4238_, v_mvarId_4239_);
v___x_4245_ = lean_apply_4(v_toBind_4241_, lean_box(0), lean_box(0), v___x_4244_, v___f_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_mvarId_4249_, lean_object* v_infoTree_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4247_, v_inst_4248_, v_mvarId_4249_, v_infoTree_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4252_, lean_object* v_output_4253_, lean_object* v_toPure_4254_, lean_object* v_____do__lift_4255_){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4256_, 0, v_____do__lift_4255_);
lean_ctor_set(v___x_4256_, 1, v_stx_4252_);
lean_ctor_set(v___x_4256_, 2, v_output_4253_);
v___x_4257_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
v___x_4258_ = lean_apply_2(v_toPure_4254_, lean_box(0), v___x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_stx_4263_, lean_object* v_output_4264_, lean_object* v_x_4265_){
_start:
{
lean_object* v_toApplicative_4266_; lean_object* v_toBind_4267_; lean_object* v_toPure_4268_; lean_object* v___f_4269_; lean_object* v_mkInfo_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; 
v_toApplicative_4266_ = lean_ctor_get(v_inst_4260_, 0);
v_toBind_4267_ = lean_ctor_get(v_inst_4260_, 1);
v_toPure_4268_ = lean_ctor_get(v_toApplicative_4266_, 1);
lean_inc_n(v_toPure_4268_, 2);
v___f_4269_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4269_, 0, v_stx_4263_);
lean_closure_set(v___f_4269_, 1, v_output_4264_);
lean_closure_set(v___f_4269_, 2, v_toPure_4268_);
lean_inc_n(v_toBind_4267_, 2);
v_mkInfo_4270_ = lean_apply_4(v_toBind_4267_, lean_box(0), lean_box(0), v_inst_4262_, v___f_4269_);
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4271_, 0, v_toPure_4268_);
lean_closure_set(v___f_4271_, 1, v_toBind_4267_);
lean_closure_set(v___f_4271_, 2, v_mkInfo_4270_);
v___x_4272_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4260_, v_inst_4261_, v_inst_4259_, v_x_4265_, v___f_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4273_, lean_object* v_00_u03b1_4274_, lean_object* v_inst_4275_, lean_object* v_inst_4276_, lean_object* v_inst_4277_, lean_object* v_inst_4278_, lean_object* v_stx_4279_, lean_object* v_output_4280_, lean_object* v_x_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4275_, v_inst_4276_, v_inst_4277_, v_inst_4278_, v_stx_4279_, v_output_4280_, v_x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4283_, lean_object* v_mvarId_4284_, lean_object* v_s_4285_){
_start:
{
lean_object* v_trees_4286_; uint8_t v_enabled_4287_; lean_object* v_assignment_4288_; lean_object* v_lazyAssignment_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4309_; 
v_trees_4286_ = lean_ctor_get(v_s_4285_, 2);
v_enabled_4287_ = lean_ctor_get_uint8(v_s_4285_, sizeof(void*)*3);
v_assignment_4288_ = lean_ctor_get(v_s_4285_, 0);
v_lazyAssignment_4289_ = lean_ctor_get(v_s_4285_, 1);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_s_4285_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4291_ = v_s_4285_;
v_isShared_4292_ = v_isSharedCheck_4309_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_trees_4286_);
lean_inc(v_lazyAssignment_4289_);
lean_inc(v_assignment_4288_);
lean_dec(v_s_4285_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4309_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v_size_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v_size_4293_ = lean_ctor_get(v_trees_4286_, 2);
v___x_4294_ = lean_unsigned_to_nat(0u);
v___x_4295_ = lean_nat_dec_lt(v___x_4294_, v_size_4293_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4297_; 
lean_dec_ref(v_trees_4286_);
lean_dec(v_mvarId_4284_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 2, v_treesSaved_4283_);
v___x_4297_ = v___x_4291_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_assignment_4288_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_lazyAssignment_4289_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_treesSaved_4283_);
lean_ctor_set_uint8(v_reuseFailAlloc_4298_, sizeof(void*)*3, v_enabled_4287_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4299_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4300_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4301_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4302_ = lean_unsigned_to_nat(1u);
v___x_4303_ = lean_nat_sub(v_size_4293_, v___x_4302_);
v___x_4304_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4301_, v_trees_4286_, v___x_4303_);
lean_dec(v___x_4303_);
lean_dec_ref(v_trees_4286_);
v___x_4305_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4299_, v___x_4300_, v_assignment_4288_, v_mvarId_4284_, v___x_4304_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 2, v_treesSaved_4283_);
lean_ctor_set(v___x_4291_, 0, v___x_4305_);
v___x_4307_ = v___x_4291_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_lazyAssignment_4289_);
lean_ctor_set(v_reuseFailAlloc_4308_, 2, v_treesSaved_4283_);
lean_ctor_set_uint8(v_reuseFailAlloc_4308_, sizeof(void*)*3, v_enabled_4287_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4310_, lean_object* v___f_4311_, lean_object* v_x_4312_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_apply_1(v_modifyInfoState_4310_, v___f_4311_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4314_, lean_object* v___f_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4314_, v___f_4315_, v_x_4316_);
lean_dec(v_x_4316_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4318_, lean_object* v_mvarId_4319_, lean_object* v_modifyInfoState_4320_, lean_object* v_inst_4321_, lean_object* v_x_4322_, lean_object* v___f_4323_, lean_object* v_treesSaved_4324_){
_start:
{
lean_object* v_toFunctor_4325_; lean_object* v_map_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_toFunctor_4325_ = lean_ctor_get(v_toApplicative_4318_, 0);
lean_inc_ref(v_toFunctor_4325_);
lean_dec_ref(v_toApplicative_4318_);
v_map_4326_ = lean_ctor_get(v_toFunctor_4325_, 0);
lean_inc(v_map_4326_);
lean_dec_ref(v_toFunctor_4325_);
v___f_4327_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4327_, 0, v_treesSaved_4324_);
lean_closure_set(v___f_4327_, 1, v_mvarId_4319_);
v___f_4328_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4328_, 0, v_modifyInfoState_4320_);
lean_closure_set(v___f_4328_, 1, v___f_4327_);
v___x_4329_ = lean_apply_4(v_inst_4321_, lean_box(0), lean_box(0), v_x_4322_, v___f_4328_);
v___x_4330_ = lean_apply_4(v_map_4326_, lean_box(0), lean_box(0), v___f_4323_, v___x_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4331_, lean_object* v_inst_4332_, lean_object* v_inst_4333_, lean_object* v_mvarId_4334_, lean_object* v_x_4335_){
_start:
{
lean_object* v_toApplicative_4336_; lean_object* v_toBind_4337_; lean_object* v_getInfoState_4338_; lean_object* v_modifyInfoState_4339_; lean_object* v___f_4340_; lean_object* v___f_4341_; lean_object* v___f_4342_; lean_object* v___x_4343_; 
v_toApplicative_4336_ = lean_ctor_get(v_inst_4332_, 0);
v_toBind_4337_ = lean_ctor_get(v_inst_4332_, 1);
lean_inc_n(v_toBind_4337_, 2);
v_getInfoState_4338_ = lean_ctor_get(v_inst_4333_, 0);
lean_inc(v_getInfoState_4338_);
v_modifyInfoState_4339_ = lean_ctor_get(v_inst_4333_, 1);
v___f_4340_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4335_);
lean_inc(v_modifyInfoState_4339_);
lean_inc_ref(v_toApplicative_4336_);
v___f_4341_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4341_, 0, v_toApplicative_4336_);
lean_closure_set(v___f_4341_, 1, v_mvarId_4334_);
lean_closure_set(v___f_4341_, 2, v_modifyInfoState_4339_);
lean_closure_set(v___f_4341_, 3, v_inst_4331_);
lean_closure_set(v___f_4341_, 4, v_x_4335_);
lean_closure_set(v___f_4341_, 5, v___f_4340_);
v___f_4342_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4342_, 0, v_x_4335_);
lean_closure_set(v___f_4342_, 1, v_inst_4332_);
lean_closure_set(v___f_4342_, 2, v_inst_4333_);
lean_closure_set(v___f_4342_, 3, v_toBind_4337_);
lean_closure_set(v___f_4342_, 4, v___f_4341_);
v___x_4343_ = lean_apply_4(v_toBind_4337_, lean_box(0), lean_box(0), v_getInfoState_4338_, v___f_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4344_, lean_object* v_00_u03b1_4345_, lean_object* v_inst_4346_, lean_object* v_inst_4347_, lean_object* v_inst_4348_, lean_object* v_mvarId_4349_, lean_object* v_x_4350_){
_start:
{
lean_object* v_toApplicative_4351_; lean_object* v_toBind_4352_; lean_object* v_getInfoState_4353_; lean_object* v_modifyInfoState_4354_; lean_object* v___f_4355_; lean_object* v___f_4356_; lean_object* v___f_4357_; lean_object* v___x_4358_; 
v_toApplicative_4351_ = lean_ctor_get(v_inst_4347_, 0);
v_toBind_4352_ = lean_ctor_get(v_inst_4347_, 1);
lean_inc_n(v_toBind_4352_, 2);
v_getInfoState_4353_ = lean_ctor_get(v_inst_4348_, 0);
lean_inc(v_getInfoState_4353_);
v_modifyInfoState_4354_ = lean_ctor_get(v_inst_4348_, 1);
v___f_4355_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4350_);
lean_inc(v_modifyInfoState_4354_);
lean_inc_ref(v_toApplicative_4351_);
v___f_4356_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4356_, 0, v_toApplicative_4351_);
lean_closure_set(v___f_4356_, 1, v_mvarId_4349_);
lean_closure_set(v___f_4356_, 2, v_modifyInfoState_4354_);
lean_closure_set(v___f_4356_, 3, v_inst_4346_);
lean_closure_set(v___f_4356_, 4, v_x_4350_);
lean_closure_set(v___f_4356_, 5, v___f_4355_);
v___f_4357_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4357_, 0, v_x_4350_);
lean_closure_set(v___f_4357_, 1, v_inst_4347_);
lean_closure_set(v___f_4357_, 2, v_inst_4348_);
lean_closure_set(v___f_4357_, 3, v_toBind_4352_);
lean_closure_set(v___f_4357_, 4, v___f_4356_);
v___x_4358_ = lean_apply_4(v_toBind_4352_, lean_box(0), lean_box(0), v_getInfoState_4353_, v___f_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4359_, lean_object* v_s_4360_){
_start:
{
lean_object* v_assignment_4361_; lean_object* v_lazyAssignment_4362_; lean_object* v_trees_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
v_assignment_4361_ = lean_ctor_get(v_s_4360_, 0);
v_lazyAssignment_4362_ = lean_ctor_get(v_s_4360_, 1);
v_trees_4363_ = lean_ctor_get(v_s_4360_, 2);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_s_4360_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v_s_4360_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_trees_4363_);
lean_inc(v_lazyAssignment_4362_);
lean_inc(v_assignment_4361_);
lean_dec(v_s_4360_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_assignment_4361_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_lazyAssignment_4362_);
lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_trees_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_ctor_set_uint8(v___x_4368_, sizeof(void*)*3, v_flag_4359_);
return v___x_4368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4371_, lean_object* v_s_4372_){
_start:
{
uint8_t v_flag_boxed_4373_; lean_object* v_res_4374_; 
v_flag_boxed_4373_ = lean_unbox(v_flag_4371_);
v_res_4374_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4373_, v_s_4372_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4375_, uint8_t v_flag_4376_){
_start:
{
lean_object* v_modifyInfoState_4377_; lean_object* v___x_4378_; lean_object* v___f_4379_; lean_object* v___x_4380_; 
v_modifyInfoState_4377_ = lean_ctor_get(v_inst_4375_, 1);
lean_inc(v_modifyInfoState_4377_);
lean_dec_ref(v_inst_4375_);
v___x_4378_ = lean_box(v_flag_4376_);
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4379_, 0, v___x_4378_);
v___x_4380_ = lean_apply_1(v_modifyInfoState_4377_, v___f_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4381_, lean_object* v_flag_4382_){
_start:
{
uint8_t v_flag_boxed_4383_; lean_object* v_res_4384_; 
v_flag_boxed_4383_ = lean_unbox(v_flag_4382_);
v_res_4384_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4381_, v_flag_boxed_4383_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4385_, lean_object* v_inst_4386_, uint8_t v_flag_4387_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4386_, v_flag_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4389_, lean_object* v_inst_4390_, lean_object* v_flag_4391_){
_start:
{
uint8_t v_flag_boxed_4392_; lean_object* v_res_4393_; 
v_flag_boxed_4392_ = lean_unbox(v_flag_4391_);
v_res_4393_ = l_Lean_Elab_enableInfoTree(v_m_4389_, v_inst_4390_, v_flag_boxed_4392_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4394_){
_start:
{
lean_object* v_fst_4395_; 
v_fst_4395_ = lean_ctor_get(v_x_4394_, 0);
lean_inc(v_fst_4395_);
return v_fst_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4396_);
lean_dec_ref(v_x_4396_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4398_, lean_object* v_____r_4399_){
_start:
{
lean_inc(v_x_4398_);
return v_x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4400_, lean_object* v_____r_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4400_, v_____r_4401_);
lean_dec(v_x_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4403_, lean_object* v_x_4404_){
_start:
{
lean_inc(v___x_4403_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4405_, lean_object* v_x_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4405_, v_x_4406_);
lean_dec(v_x_4406_);
lean_dec(v___x_4405_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4408_, lean_object* v_inst_4409_, uint8_t v_flag_4410_, lean_object* v_toBind_4411_, lean_object* v___f_4412_, lean_object* v_inst_4413_, lean_object* v___f_4414_, lean_object* v_____do__lift_4415_){
_start:
{
uint8_t v_enabled_4416_; lean_object* v_map_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___f_4421_; lean_object* v_y_4422_; lean_object* v___x_4423_; 
v_enabled_4416_ = lean_ctor_get_uint8(v_____do__lift_4415_, sizeof(void*)*3);
v_map_4417_ = lean_ctor_get(v_toFunctor_4408_, 0);
lean_inc(v_map_4417_);
lean_dec_ref(v_toFunctor_4408_);
lean_inc_ref(v_inst_4409_);
v___x_4418_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4409_, v_flag_4410_);
v___x_4419_ = lean_apply_4(v_toBind_4411_, lean_box(0), lean_box(0), v___x_4418_, v___f_4412_);
v___x_4420_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4409_, v_enabled_4416_);
v___f_4421_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4421_, 0, v___x_4420_);
v_y_4422_ = lean_apply_4(v_inst_4413_, lean_box(0), lean_box(0), v___x_4419_, v___f_4421_);
v___x_4423_ = lean_apply_4(v_map_4417_, lean_box(0), lean_box(0), v___f_4414_, v_y_4422_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4424_, lean_object* v_inst_4425_, lean_object* v_flag_4426_, lean_object* v_toBind_4427_, lean_object* v___f_4428_, lean_object* v_inst_4429_, lean_object* v___f_4430_, lean_object* v_____do__lift_4431_){
_start:
{
uint8_t v_flag_boxed_4432_; lean_object* v_res_4433_; 
v_flag_boxed_4432_ = lean_unbox(v_flag_4426_);
v_res_4433_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4424_, v_inst_4425_, v_flag_boxed_4432_, v_toBind_4427_, v___f_4428_, v_inst_4429_, v___f_4430_, v_____do__lift_4431_);
lean_dec_ref(v_____do__lift_4431_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4435_, lean_object* v_inst_4436_, lean_object* v_inst_4437_, uint8_t v_flag_4438_, lean_object* v_x_4439_){
_start:
{
lean_object* v_toApplicative_4440_; lean_object* v_toBind_4441_; lean_object* v_getInfoState_4442_; lean_object* v_toFunctor_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___x_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; 
v_toApplicative_4440_ = lean_ctor_get(v_inst_4435_, 0);
lean_inc_ref(v_toApplicative_4440_);
v_toBind_4441_ = lean_ctor_get(v_inst_4435_, 1);
lean_inc_n(v_toBind_4441_, 2);
lean_dec_ref(v_inst_4435_);
v_getInfoState_4442_ = lean_ctor_get(v_inst_4436_, 0);
lean_inc(v_getInfoState_4442_);
v_toFunctor_4443_ = lean_ctor_get(v_toApplicative_4440_, 0);
lean_inc_ref(v_toFunctor_4443_);
lean_dec_ref(v_toApplicative_4440_);
v___f_4444_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4445_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4445_, 0, v_x_4439_);
v___x_4446_ = lean_box(v_flag_4438_);
v___f_4447_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4447_, 0, v_toFunctor_4443_);
lean_closure_set(v___f_4447_, 1, v_inst_4436_);
lean_closure_set(v___f_4447_, 2, v___x_4446_);
lean_closure_set(v___f_4447_, 3, v_toBind_4441_);
lean_closure_set(v___f_4447_, 4, v___f_4445_);
lean_closure_set(v___f_4447_, 5, v_inst_4437_);
lean_closure_set(v___f_4447_, 6, v___f_4444_);
v___x_4448_ = lean_apply_4(v_toBind_4441_, lean_box(0), lean_box(0), v_getInfoState_4442_, v___f_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4449_, lean_object* v_inst_4450_, lean_object* v_inst_4451_, lean_object* v_flag_4452_, lean_object* v_x_4453_){
_start:
{
uint8_t v_flag_boxed_4454_; lean_object* v_res_4455_; 
v_flag_boxed_4454_ = lean_unbox(v_flag_4452_);
v_res_4455_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4449_, v_inst_4450_, v_inst_4451_, v_flag_boxed_4454_, v_x_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4456_, lean_object* v_00_u03b1_4457_, lean_object* v_inst_4458_, lean_object* v_inst_4459_, lean_object* v_inst_4460_, uint8_t v_flag_4461_, lean_object* v_x_4462_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4458_, v_inst_4459_, v_inst_4460_, v_flag_4461_, v_x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4464_, lean_object* v_00_u03b1_4465_, lean_object* v_inst_4466_, lean_object* v_inst_4467_, lean_object* v_inst_4468_, lean_object* v_flag_4469_, lean_object* v_x_4470_){
_start:
{
uint8_t v_flag_boxed_4471_; lean_object* v_res_4472_; 
v_flag_boxed_4471_ = lean_unbox(v_flag_4469_);
v_res_4472_ = l_Lean_Elab_withEnableInfoTree(v_m_4464_, v_00_u03b1_4465_, v_inst_4466_, v_inst_4467_, v_inst_4468_, v_flag_boxed_4471_, v_x_4470_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4473_, lean_object* v_____do__lift_4474_){
_start:
{
lean_object* v_trees_4475_; lean_object* v___x_4476_; 
v_trees_4475_ = lean_ctor_get(v_____do__lift_4474_, 2);
lean_inc_ref(v_trees_4475_);
lean_dec_ref(v_____do__lift_4474_);
v___x_4476_ = lean_apply_2(v_toPure_4473_, lean_box(0), v_trees_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4477_, lean_object* v_inst_4478_){
_start:
{
lean_object* v_toApplicative_4479_; lean_object* v_toBind_4480_; lean_object* v_getInfoState_4481_; lean_object* v_toPure_4482_; lean_object* v___f_4483_; lean_object* v___x_4484_; 
v_toApplicative_4479_ = lean_ctor_get(v_inst_4478_, 0);
lean_inc_ref(v_toApplicative_4479_);
v_toBind_4480_ = lean_ctor_get(v_inst_4478_, 1);
lean_inc(v_toBind_4480_);
lean_dec_ref(v_inst_4478_);
v_getInfoState_4481_ = lean_ctor_get(v_inst_4477_, 0);
lean_inc(v_getInfoState_4481_);
lean_dec_ref(v_inst_4477_);
v_toPure_4482_ = lean_ctor_get(v_toApplicative_4479_, 1);
lean_inc(v_toPure_4482_);
lean_dec_ref(v_toApplicative_4479_);
v___f_4483_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4483_, 0, v_toPure_4482_);
v___x_4484_ = lean_apply_4(v_toBind_4480_, lean_box(0), lean_box(0), v_getInfoState_4481_, v___f_4483_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4485_, lean_object* v_inst_4486_, lean_object* v_inst_4487_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4486_, v_inst_4487_);
return v___x_4488_;
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
