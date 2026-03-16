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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6;
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
lean_inc(v_toBind_70_);
lean_dec_ref(v_inst_63_);
v_getEnv_71_ = lean_ctor_get(v_inst_64_, 0);
lean_inc(v_getEnv_71_);
lean_dec_ref(v_inst_64_);
v_toPure_72_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_72_);
lean_dec_ref(v_toApplicative_69_);
lean_inc(v_toBind_70_);
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
lean_inc(v_toBind_116_);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_toPure_117_);
v___x_118_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_);
lean_inc(v_toBind_116_);
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
v___x_132_ = lean_panic_fn(v___x_131_, v_msg_130_);
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
return v_b_297_;
}
else
{
lean_object* v___x_299_; lean_object* v_a_300_; lean_object* v___x_301_; 
lean_dec_ref(v_b_297_);
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
return v_b_312_;
}
else
{
lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_316_; 
lean_dec_ref(v_b_312_);
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
lean_inc_ref(v_i_356_);
v_children_357_ = lean_ctor_get(v_t_353_, 1);
lean_inc_ref(v_children_357_);
lean_dec_ref(v_t_353_);
lean_inc_ref(v_p_352_);
lean_inc_ref(v_i_356_);
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
lean_object* v_es_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_434_; 
v_es_413_ = lean_ctor_get(v_x_410_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_434_ == 0)
{
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_434_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_es_413_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_434_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v_j_421_; lean_object* v___x_422_; 
v___x_417_ = lean_box(2);
v___x_418_ = ((size_t)5ULL);
v___x_419_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1);
v___x_420_ = lean_usize_land(v_x_411_, v___x_419_);
v_j_421_ = lean_usize_to_nat(v___x_420_);
v___x_422_ = lean_array_get(v___x_417_, v_es_413_, v_j_421_);
lean_dec(v_j_421_);
lean_dec_ref(v_es_413_);
switch(lean_obj_tag(v___x_422_))
{
case 0:
{
lean_object* v_key_423_; lean_object* v_val_424_; uint8_t v___x_425_; 
v_key_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_key_423_);
v_val_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_val_424_);
lean_dec_ref(v___x_422_);
v___x_425_ = l_Lean_instBEqMVarId_beq(v_x_412_, v_key_423_);
lean_dec(v_key_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec(v_val_424_);
lean_del_object(v___x_415_);
v___x_426_ = lean_box(0);
return v___x_426_;
}
else
{
lean_object* v___x_428_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 1);
lean_ctor_set(v___x_415_, 0, v_val_424_);
v___x_428_ = v___x_415_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_val_424_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
case 1:
{
lean_object* v_node_430_; size_t v___x_431_; 
lean_del_object(v___x_415_);
v_node_430_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_node_430_);
lean_dec_ref(v___x_422_);
v___x_431_ = lean_usize_shift_right(v_x_411_, v___x_418_);
v_x_410_ = v_node_430_;
v_x_411_ = v___x_431_;
goto _start;
}
default: 
{
lean_object* v___x_433_; 
lean_del_object(v___x_415_);
v___x_433_ = lean_box(0);
return v___x_433_;
}
}
}
}
else
{
lean_object* v_ks_435_; lean_object* v_vs_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_ks_435_ = lean_ctor_get(v_x_410_, 0);
lean_inc_ref(v_ks_435_);
v_vs_436_ = lean_ctor_get(v_x_410_, 1);
lean_inc_ref(v_vs_436_);
lean_dec_ref(v_x_410_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_ks_435_, v_vs_436_, v___x_437_, v_x_412_);
lean_dec_ref(v_vs_436_);
lean_dec_ref(v_ks_435_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
size_t v_x_693__boxed_442_; lean_object* v_res_443_; 
v_x_693__boxed_442_ = lean_unbox_usize(v_x_440_);
lean_dec(v_x_440_);
v_res_443_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_439_, v_x_693__boxed_442_, v_x_441_);
lean_dec(v_x_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
uint64_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = l_Lean_instHashableMVarId_hash(v_x_445_);
v___x_447_ = lean_uint64_to_usize(v___x_446_);
v___x_448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_444_, v___x_447_, v_x_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg___boxed(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_449_, v_x_450_);
lean_dec(v_x_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(lean_object* v_assignment_452_, size_t v_sz_453_, size_t v_i_454_, lean_object* v_bs_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_assignment_452_);
return v_bs_455_;
}
else
{
lean_object* v_v_457_; lean_object* v___x_458_; lean_object* v_bs_x27_459_; lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; lean_object* v___x_463_; 
v_v_457_ = lean_array_uget(v_bs_455_, v_i_454_);
v___x_458_ = lean_unsigned_to_nat(0u);
v_bs_x27_459_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_458_);
lean_inc_ref(v_assignment_452_);
v___x_460_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_452_, v_v_457_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_454_, v___x_461_);
v___x_463_ = lean_array_uset(v_bs_x27_459_, v_i_454_, v___x_460_);
v_i_454_ = v___x_462_;
v_bs_455_ = v___x_463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_substitute(lean_object* v_tree_465_, lean_object* v_assignment_466_){
_start:
{
switch(lean_obj_tag(v_tree_465_))
{
case 0:
{
lean_object* v_i_467_; lean_object* v_t_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_476_; 
v_i_467_ = lean_ctor_get(v_tree_465_, 0);
v_t_468_ = lean_ctor_get(v_tree_465_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_tree_465_);
if (v_isSharedCheck_476_ == 0)
{
v___x_470_ = v_tree_465_;
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_t_468_);
lean_inc(v_i_467_);
lean_dec(v_tree_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = l_Lean_Elab_InfoTree_substitute(v_t_468_, v_assignment_466_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_472_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_i_467_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
case 1:
{
lean_object* v_i_477_; lean_object* v_children_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_i_477_ = lean_ctor_get(v_tree_465_, 0);
v_children_478_ = lean_ctor_get(v_tree_465_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_tree_465_);
if (v_isSharedCheck_486_ == 0)
{
v___x_480_ = v_tree_465_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_children_478_);
lean_inc(v_i_477_);
lean_dec(v_tree_465_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(v_assignment_466_, v_children_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_i_477_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
default: 
{
lean_object* v_mvarId_487_; lean_object* v___x_488_; 
v_mvarId_487_ = lean_ctor_get(v_tree_465_, 0);
lean_inc_ref(v_assignment_466_);
v___x_488_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_assignment_466_, v_mvarId_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref(v_assignment_466_);
return v_tree_465_;
}
else
{
lean_object* v_val_489_; 
lean_dec_ref(v_tree_465_);
v_val_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_val_489_);
lean_dec_ref(v___x_488_);
v_tree_465_ = v_val_489_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(lean_object* v_assignment_491_, size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_assignment_491_);
return v_bs_494_;
}
else
{
lean_object* v_v_496_; lean_object* v___x_497_; lean_object* v_bs_x27_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v_v_496_ = lean_array_uget(v_bs_494_, v_i_493_);
v___x_497_ = lean_unsigned_to_nat(0u);
v_bs_x27_498_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_497_);
lean_inc_ref(v_assignment_491_);
v___x_499_ = l_Lean_Elab_InfoTree_substitute(v_v_496_, v_assignment_491_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_493_, v___x_500_);
v___x_502_ = lean_array_uset(v_bs_x27_498_, v_i_493_, v___x_499_);
v_i_493_ = v___x_501_;
v_bs_494_ = v___x_502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(lean_object* v_assignment_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_cs_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_cs_506_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v_x_505_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_cs_506_);
lean_dec(v_x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
size_t v_sz_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v_sz_510_ = lean_array_size(v_cs_506_);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_504_, v_sz_510_, v___x_511_, v_cs_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_vs_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_527_; 
v_vs_517_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_527_ == 0)
{
v___x_519_ = v_x_505_;
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_vs_517_);
lean_dec(v_x_505_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
size_t v_sz_521_; size_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v_sz_521_ = lean_array_size(v_vs_517_);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_504_, v_sz_521_, v___x_522_, v_vs_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_525_ = v___x_519_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(lean_object* v_assignment_528_, lean_object* v_t_529_){
_start:
{
lean_object* v_root_530_; lean_object* v_tail_531_; lean_object* v_size_532_; size_t v_shift_533_; lean_object* v_tailOff_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_root_530_ = lean_ctor_get(v_t_529_, 0);
v_tail_531_ = lean_ctor_get(v_t_529_, 1);
v_size_532_ = lean_ctor_get(v_t_529_, 2);
v_shift_533_ = lean_ctor_get_usize(v_t_529_, 4);
v_tailOff_534_ = lean_ctor_get(v_t_529_, 3);
v_isSharedCheck_545_ = !lean_is_exclusive(v_t_529_);
if (v_isSharedCheck_545_ == 0)
{
v___x_536_ = v_t_529_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_tailOff_534_);
lean_inc(v_size_532_);
lean_inc(v_tail_531_);
lean_inc(v_root_530_);
lean_dec(v_t_529_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; size_t v_sz_539_; size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc_ref(v_assignment_528_);
v___x_538_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_528_, v_root_530_);
v_sz_539_ = lean_array_size(v_tail_531_);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_528_, v_sz_539_, v___x_540_, v_tail_531_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_541_);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_size_532_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_tailOff_534_);
lean_ctor_set_usize(v_reuseFailAlloc_544_, 4, v_shift_533_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
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
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(lean_object* v_00_u03b2_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_x_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___boxed(lean_object* v_00_u03b2_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(v_00_u03b2_564_, v_x_565_, v_x_566_);
lean_dec(v_x_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(lean_object* v_00_u03b2_568_, lean_object* v_x_569_, size_t v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_569_, v_x_570_, v_x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___boxed(lean_object* v_00_u03b2_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
size_t v_x_916__boxed_577_; lean_object* v_res_578_; 
v_x_916__boxed_577_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_res_578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(v_00_u03b2_573_, v_x_574_, v_x_916__boxed_577_, v_x_576_);
lean_dec(v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_579_, lean_object* v_keys_580_, lean_object* v_vals_581_, lean_object* v_heq_582_, lean_object* v_i_583_, lean_object* v_k_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_580_, v_vals_581_, v_i_583_, v_k_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_586_, lean_object* v_keys_587_, lean_object* v_vals_588_, lean_object* v_heq_589_, lean_object* v_i_590_, lean_object* v_k_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(v_00_u03b2_586_, v_keys_587_, v_vals_588_, v_heq_589_, v_i_590_, v_k_591_);
lean_dec(v_k_591_);
lean_dec_ref(v_vals_588_);
lean_dec_ref(v_keys_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(lean_object* v_f_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_acc_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_as_594_);
v___x_598_ = lean_nat_dec_eq(v_i_595_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_599_ = lean_array_fget_borrowed(v_as_594_, v_i_595_);
lean_inc(v_f_593_);
lean_inc(v___x_599_);
v___x_600_ = lean_apply_1(v_f_593_, v___x_599_);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_i_595_, v___x_601_);
lean_dec(v_i_595_);
v___x_603_ = lean_array_push(v_acc_596_, v___x_600_);
v_i_595_ = v___x_602_;
v_acc_596_ = v___x_603_;
goto _start;
}
else
{
lean_dec(v_i_595_);
lean_dec(v_f_593_);
return v_acc_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_f_605_, lean_object* v_as_606_, lean_object* v_i_607_, lean_object* v_acc_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_605_, v_as_606_, v_i_607_, v_acc_608_);
lean_dec_ref(v_as_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_610_, lean_object* v_as_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_array_get_size(v_as_611_);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_610_, v_as_611_, v___x_612_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_616_, lean_object* v_as_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_616_, v_as_617_);
lean_dec_ref(v_as_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_bs_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
lean_dec(v_f_619_);
return v_bs_622_;
}
else
{
lean_object* v_v_624_; lean_object* v___x_625_; lean_object* v_bs_x27_626_; lean_object* v___y_628_; 
v_v_624_ = lean_array_uget(v_bs_622_, v_i_621_);
v___x_625_ = lean_unsigned_to_nat(0u);
v_bs_x27_626_ = lean_array_uset(v_bs_622_, v_i_621_, v___x_625_);
switch(lean_obj_tag(v_v_624_))
{
case 0:
{
lean_object* v_key_633_; lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
v_key_633_ = lean_ctor_get(v_v_624_, 0);
v_val_634_ = lean_ctor_get(v_v_624_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_v_624_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v_v_624_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_inc(v_key_633_);
lean_dec(v_v_624_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
lean_inc(v_f_619_);
v___x_638_ = lean_apply_1(v_f_619_, v_val_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_key_633_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v___y_628_ = v___x_640_;
goto v___jp_627_;
}
}
}
case 1:
{
lean_object* v_node_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_node_643_ = lean_ctor_get(v_v_624_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_v_624_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_v_624_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_node_643_);
lean_dec(v_v_624_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
lean_inc(v_f_619_);
v___x_647_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_619_, v_node_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_628_ = v___x_649_;
goto v___jp_627_;
}
}
}
default: 
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(2);
v___y_628_ = v___x_652_;
goto v___jp_627_;
}
}
v___jp_627_:
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_621_, v___x_629_);
v___x_631_ = lean_array_uset(v_bs_x27_626_, v_i_621_, v___y_628_);
v_i_621_ = v___x_630_;
v_bs_622_ = v___x_631_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(lean_object* v_f_653_, lean_object* v_n_654_){
_start:
{
if (lean_obj_tag(v_n_654_) == 0)
{
lean_object* v_es_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_665_; 
v_es_655_ = lean_ctor_get(v_n_654_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_n_654_);
if (v_isSharedCheck_665_ == 0)
{
v___x_657_ = v_n_654_;
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_es_655_);
lean_dec(v_n_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v_sz_659_ = lean_array_size(v_es_655_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_653_, v_sz_659_, v___x_660_, v_es_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_661_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_ks_666_; lean_object* v_vs_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_ks_666_ = lean_ctor_get(v_n_654_, 0);
v_vs_667_ = lean_ctor_get(v_n_654_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_n_654_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_n_654_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_vs_667_);
lean_inc(v_ks_666_);
lean_dec(v_n_654_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_val_671_; lean_object* v___x_673_; 
v_val_671_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_653_, v_vs_667_);
lean_dec_ref(v_vs_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v_val_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_ks_666_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_val_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_bs_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_676_, v_sz_boxed_680_, v_i_boxed_681_, v_bs_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0(lean_object* v_f_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_apply_1(v_f_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(lean_object* v_pm_686_, lean_object* v_f_687_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; 
v___f_688_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_688_, 0, v_f_687_);
v___x_689_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v___f_688_, v_pm_686_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0(lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_task_get_own(v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(lean_object* v_s_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_bs_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_s_693_);
return v_bs_696_;
}
else
{
lean_object* v_lazyAssignment_698_; lean_object* v_v_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v_bs_x27_702_; lean_object* v___x_703_; lean_object* v___x_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v_lazyAssignment_698_ = lean_ctor_get(v_s_693_, 1);
v_v_699_ = lean_array_uget(v_bs_696_, v_i_695_);
v___f_700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0));
v___x_701_ = lean_unsigned_to_nat(0u);
v_bs_x27_702_ = lean_array_uset(v_bs_696_, v_i_695_, v___x_701_);
lean_inc_ref(v_lazyAssignment_698_);
v___x_703_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_lazyAssignment_698_, v___f_700_);
v___x_704_ = l_Lean_Elab_InfoTree_substitute(v_v_699_, v___x_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_695_, v___x_705_);
v___x_707_ = lean_array_uset(v_bs_x27_702_, v_i_695_, v___x_704_);
v_i_695_ = v___x_706_;
v_bs_696_ = v___x_707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___boxed(lean_object* v_s_709_, lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_709_, v_sz_boxed_713_, v_i_boxed_714_, v_bs_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(lean_object* v_s_716_, size_t v_sz_717_, size_t v_i_718_, lean_object* v_bs_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_718_, v_sz_717_);
if (v___x_720_ == 0)
{
lean_dec_ref(v_s_716_);
return v_bs_719_;
}
else
{
lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; lean_object* v___x_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_v_721_ = lean_array_uget(v_bs_719_, v_i_718_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_719_, v_i_718_, v___x_722_);
lean_inc_ref(v_s_716_);
v___x_724_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_716_, v_v_721_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_718_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_723_, v_i_718_, v___x_724_);
v_i_718_ = v___x_726_;
v_bs_719_ = v___x_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(lean_object* v_s_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
lean_object* v_cs_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v_cs_731_ = lean_ctor_get(v_x_730_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_730_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v_x_730_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_cs_731_);
lean_dec(v_x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
size_t v_sz_735_; size_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v_sz_735_ = lean_array_size(v_cs_731_);
v___x_736_ = ((size_t)0ULL);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_729_, v_sz_735_, v___x_736_, v_cs_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_737_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_object* v_vs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_752_; 
v_vs_742_ = lean_ctor_get(v_x_730_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_730_);
if (v_isSharedCheck_752_ == 0)
{
v___x_744_ = v_x_730_;
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_vs_742_);
lean_dec(v_x_730_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
size_t v_sz_746_; size_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v_sz_746_ = lean_array_size(v_vs_742_);
v___x_747_ = ((size_t)0ULL);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_729_, v_sz_746_, v___x_747_, v_vs_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_750_ = v___x_744_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4___boxed(lean_object* v_s_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_bs_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_753_, v_sz_boxed_757_, v_i_boxed_758_, v_bs_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(lean_object* v_s_760_, lean_object* v_t_761_){
_start:
{
lean_object* v_root_762_; lean_object* v_tail_763_; lean_object* v_size_764_; size_t v_shift_765_; lean_object* v_tailOff_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_777_; 
v_root_762_ = lean_ctor_get(v_t_761_, 0);
v_tail_763_ = lean_ctor_get(v_t_761_, 1);
v_size_764_ = lean_ctor_get(v_t_761_, 2);
v_shift_765_ = lean_ctor_get_usize(v_t_761_, 4);
v_tailOff_766_ = lean_ctor_get(v_t_761_, 3);
v_isSharedCheck_777_ = !lean_is_exclusive(v_t_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_768_ = v_t_761_;
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_tailOff_766_);
lean_inc(v_size_764_);
lean_inc(v_tail_763_);
lean_inc(v_root_762_);
lean_dec(v_t_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc_ref(v_s_760_);
v___x_770_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_760_, v_root_762_);
v_sz_771_ = lean_array_size(v_tail_763_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_760_, v_sz_771_, v___x_772_, v_tail_763_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_773_);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_size_764_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_tailOff_766_);
lean_ctor_set_usize(v_reuseFailAlloc_776_, 4, v_shift_765_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0(lean_object* v_s_781_, lean_object* v_trees_782_, uint8_t v_enabled_783_, lean_object* v_assignment_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1, &l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once, _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1);
v___x_787_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(v_s_781_, v_trees_782_);
v___x_788_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_788_, 0, v_assignment_784_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
lean_ctor_set(v___x_788_, 2, v___x_787_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*3, v_enabled_783_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed(lean_object* v_s_789_, lean_object* v_trees_790_, lean_object* v_enabled_791_, lean_object* v_assignment_792_, lean_object* v_x_793_){
_start:
{
uint8_t v_enabled_boxed_794_; lean_object* v_res_795_; 
v_enabled_boxed_794_ = lean_unbox(v_enabled_791_);
v_res_795_ = l_Lean_Elab_InfoState_substituteLazy___lam__0(v_s_789_, v_trees_790_, v_enabled_boxed_794_, v_assignment_792_, v_x_793_);
lean_dec(v_x_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0(lean_object* v_f_796_, lean_object* v_x1_797_, lean_object* v_x2_798_, lean_object* v_x3_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_apply_3(v_f_796_, v_x1_797_, v_x2_798_, v_x3_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_f_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_i_804_, lean_object* v_acc_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_array_get_size(v_keys_802_);
v___x_807_ = lean_nat_dec_lt(v_i_804_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_i_804_);
lean_dec(v_f_801_);
return v_acc_805_;
}
else
{
lean_object* v_k_808_; lean_object* v_v_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_k_808_ = lean_array_fget_borrowed(v_keys_802_, v_i_804_);
v_v_809_ = lean_array_fget_borrowed(v_vals_803_, v_i_804_);
lean_inc(v_f_801_);
lean_inc(v_v_809_);
lean_inc(v_k_808_);
v___x_810_ = lean_apply_3(v_f_801_, v_acc_805_, v_k_808_, v_v_809_);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_i_804_, v___x_811_);
lean_dec(v_i_804_);
v_i_804_ = v___x_812_;
v_acc_805_ = v___x_810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_f_814_, lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_i_817_, lean_object* v_acc_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_814_, v_keys_815_, v_vals_816_, v_i_817_, v_acc_818_);
lean_dec_ref(v_vals_816_);
lean_dec_ref(v_keys_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_f_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v_es_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_es_823_ = lean_ctor_get(v_x_821_, 0);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_array_get_size(v_es_823_);
v___x_826_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec(v_f_820_);
return v_x_822_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_le(v___x_825_, v___x_825_);
if (v___x_827_ == 0)
{
if (v___x_826_ == 0)
{
lean_dec(v_f_820_);
return v_x_822_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_825_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_820_, v_es_823_, v___x_828_, v___x_829_, v_x_822_);
return v___x_830_;
}
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_825_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_820_, v_es_823_, v___x_831_, v___x_832_, v_x_822_);
return v___x_833_;
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_ks_834_ = lean_ctor_get(v_x_821_, 0);
v_vs_835_ = lean_ctor_get(v_x_821_, 1);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_820_, v_ks_834_, v_vs_835_, v___x_836_, v_x_822_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(lean_object* v_f_838_, lean_object* v_as_839_, size_t v_i_840_, size_t v_stop_841_, lean_object* v_b_842_){
_start:
{
lean_object* v___y_844_; uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_eq(v_i_840_, v_stop_841_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_array_uget_borrowed(v_as_839_, v_i_840_);
switch(lean_obj_tag(v___x_849_))
{
case 0:
{
lean_object* v_key_850_; lean_object* v_val_851_; lean_object* v___x_852_; 
v_key_850_ = lean_ctor_get(v___x_849_, 0);
v_val_851_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_f_838_);
lean_inc(v_val_851_);
lean_inc(v_key_850_);
v___x_852_ = lean_apply_3(v_f_838_, v_b_842_, v_key_850_, v_val_851_);
v___y_844_ = v___x_852_;
goto v___jp_843_;
}
case 1:
{
lean_object* v_node_853_; lean_object* v___x_854_; 
v_node_853_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_f_838_);
v___x_854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_838_, v_node_853_, v_b_842_);
v___y_844_ = v___x_854_;
goto v___jp_843_;
}
default: 
{
v___y_844_ = v_b_842_;
goto v___jp_843_;
}
}
}
else
{
lean_dec(v_f_838_);
return v_b_842_;
}
v___jp_843_:
{
size_t v___x_845_; size_t v___x_846_; 
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_840_, v___x_845_);
v_i_840_ = v___x_846_;
v_b_842_ = v___y_844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg___boxed(lean_object* v_f_855_, lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_){
_start:
{
size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v_i_boxed_860_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_855_, v_as_856_, v_i_boxed_860_, v_stop_boxed_861_, v_b_859_);
lean_dec_ref(v_as_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_f_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_863_, v_x_864_, v_x_865_);
lean_dec_ref(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(lean_object* v_map_867_, lean_object* v_f_868_, lean_object* v_init_869_){
_start:
{
lean_object* v___f_870_; lean_object* v___x_871_; 
v___f_870_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0), 4, 1);
lean_closure_set(v___f_870_, 0, v_f_868_);
v___x_871_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v___f_870_, v_map_867_, v_init_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___boxed(lean_object* v_map_872_, lean_object* v_f_873_, lean_object* v_init_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_872_, v_f_873_, v_init_874_);
lean_dec_ref(v_map_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0(lean_object* v_ps_876_, lean_object* v_k_877_, lean_object* v_v_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_k_877_);
lean_ctor_set(v___x_879_, 1, v_v_878_);
v___x_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_ps_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(lean_object* v_m_882_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___f_883_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0));
v___x_884_ = lean_box(0);
v___x_885_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_m_882_, v___f_883_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___boxed(lean_object* v_m_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_886_);
lean_dec_ref(v_m_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v___x_890_; 
v___x_890_ = l_List_reverse___redArg(v_a_889_);
return v___x_890_;
}
else
{
lean_object* v_head_891_; lean_object* v_tail_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_901_; 
v_head_891_ = lean_ctor_get(v_a_888_, 0);
v_tail_892_ = lean_ctor_get(v_a_888_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_901_ == 0)
{
v___x_894_ = v_a_888_;
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_tail_892_);
lean_inc(v_head_891_);
lean_dec(v_a_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_snd_896_; lean_object* v___x_898_; 
v_snd_896_ = lean_ctor_get(v_head_891_, 1);
lean_inc(v_snd_896_);
lean_dec(v_head_891_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_a_889_);
lean_ctor_set(v___x_894_, 0, v_snd_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_snd_896_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_889_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
v_a_888_ = v_tail_892_;
v_a_889_ = v___x_898_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object* v_s_902_){
_start:
{
uint8_t v_enabled_903_; lean_object* v_assignment_904_; lean_object* v_lazyAssignment_905_; lean_object* v_trees_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v_enabled_903_ = lean_ctor_get_uint8(v_s_902_, sizeof(void*)*3);
v_assignment_904_ = lean_ctor_get(v_s_902_, 0);
lean_inc_ref(v_assignment_904_);
v_lazyAssignment_905_ = lean_ctor_get(v_s_902_, 1);
lean_inc_ref(v_lazyAssignment_905_);
v_trees_906_ = lean_ctor_get(v_s_902_, 2);
lean_inc_ref(v_trees_906_);
v___x_907_ = lean_box(v_enabled_903_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed), 5, 4);
lean_closure_set(v___f_908_, 0, v_s_902_);
lean_closure_set(v___f_908_, 1, v_trees_906_);
lean_closure_set(v___f_908_, 2, v___x_907_);
lean_closure_set(v___f_908_, 3, v_assignment_904_);
v___x_909_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_lazyAssignment_905_);
lean_dec_ref(v_lazyAssignment_905_);
v___x_910_ = lean_box(0);
v___x_911_ = l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(v___x_909_, v___x_910_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = 0;
v___x_914_ = l_Task_mapList___redArg(v___f_908_, v___x_911_, v___x_912_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0(lean_object* v_00_u03b2_915_, lean_object* v_00_u03c3_916_, lean_object* v_pm_917_, lean_object* v_f_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_pm_917_, v_f_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(lean_object* v_00_u03b2_920_, lean_object* v_m_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___boxed(lean_object* v_00_u03b2_923_, lean_object* v_m_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(v_00_u03b2_923_, v_m_924_);
lean_dec_ref(v_m_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0___redArg(lean_object* v_pm_926_, lean_object* v_f_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_927_, v_pm_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0(lean_object* v_00_u03b2_929_, lean_object* v_00_u03c3_930_, lean_object* v_pm_931_, lean_object* v_f_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_932_, v_pm_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(lean_object* v_00_u03c3_934_, lean_object* v_00_u03b2_935_, lean_object* v_map_936_, lean_object* v_f_937_, lean_object* v_init_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_936_, v_f_937_, v_init_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___boxed(lean_object* v_00_u03c3_940_, lean_object* v_00_u03b2_941_, lean_object* v_map_942_, lean_object* v_f_943_, lean_object* v_init_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(v_00_u03c3_940_, v_00_u03b2_941_, v_map_942_, v_f_943_, v_init_944_);
lean_dec_ref(v_map_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_00_u03c3_948_, lean_object* v_f_949_, lean_object* v_n_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_949_, v_n_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(lean_object* v_map_952_, lean_object* v_f_953_, lean_object* v_init_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_953_, v_map_952_, v_init_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_map_956_, lean_object* v_f_957_, lean_object* v_init_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(v_map_956_, v_f_957_, v_init_958_);
lean_dec_ref(v_map_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_960_, lean_object* v_00_u03b2_961_, lean_object* v_map_962_, lean_object* v_f_963_, lean_object* v_init_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_963_, v_map_962_, v_init_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_966_, lean_object* v_00_u03b2_967_, lean_object* v_map_968_, lean_object* v_f_969_, lean_object* v_init_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(v_00_u03c3_966_, v_00_u03b2_967_, v_map_968_, v_f_969_, v_init_970_);
lean_dec_ref(v_map_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_00_u03c3_974_, lean_object* v_f_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_975_, v_sz_976_, v_i_977_, v_bs_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_00_u03c3_982_, lean_object* v_f_983_, lean_object* v_sz_984_, lean_object* v_i_985_, lean_object* v_bs_986_){
_start:
{
size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_sz_boxed_987_ = lean_unbox_usize(v_sz_984_);
lean_dec(v_sz_984_);
v_i_boxed_988_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_980_, v_00_u03b2_981_, v_00_u03c3_982_, v_f_983_, v_sz_boxed_987_, v_i_boxed_988_, v_bs_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_f_992_, lean_object* v_as_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_992_, v_as_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_f_997_, lean_object* v_as_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_995_, v_00_u03b2_996_, v_f_997_, v_as_998_);
lean_dec_ref(v_as_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_1000_, lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_f_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03c3_1007_, lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_f_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(v_00_u03c3_1007_, v_00_u03b1_1008_, v_00_u03b2_1009_, v_f_1010_, v_x_1011_, v_x_1012_);
lean_dec_ref(v_x_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_f_1016_, lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_acc_1019_, lean_object* v_hle_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_1016_, v_as_1017_, v_i_1018_, v_acc_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_f_1024_, lean_object* v_as_1025_, lean_object* v_i_1026_, lean_object* v_acc_1027_, lean_object* v_hle_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_1022_, v_00_u03b2_1023_, v_f_1024_, v_as_1025_, v_i_1026_, v_acc_1027_, v_hle_1028_);
lean_dec_ref(v_as_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_00_u03c3_1032_, lean_object* v_f_1033_, lean_object* v_as_1034_, size_t v_i_1035_, size_t v_stop_1036_, lean_object* v_b_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_1033_, v_as_1034_, v_i_1035_, v_stop_1036_, v_b_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_00_u03c3_1041_, lean_object* v_f_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_, lean_object* v_b_1046_){
_start:
{
size_t v_i_boxed_1047_; size_t v_stop_boxed_1048_; lean_object* v_res_1049_; 
v_i_boxed_1047_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1048_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(v_00_u03b1_1039_, v_00_u03b2_1040_, v_00_u03c3_1041_, v_f_1042_, v_as_1043_, v_i_boxed_1047_, v_stop_boxed_1048_, v_b_1046_);
lean_dec_ref(v_as_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03c3_1050_, lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_f_1053_, lean_object* v_keys_1054_, lean_object* v_vals_1055_, lean_object* v_heq_1056_, lean_object* v_i_1057_, lean_object* v_acc_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_1053_, v_keys_1054_, v_vals_1055_, v_i_1057_, v_acc_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03c3_1060_, lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_f_1063_, lean_object* v_keys_1064_, lean_object* v_vals_1065_, lean_object* v_heq_1066_, lean_object* v_i_1067_, lean_object* v_acc_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(v_00_u03c3_1060_, v_00_u03b1_1061_, v_00_u03b2_1062_, v_f_1063_, v_keys_1064_, v_vals_1065_, v_heq_1066_, v_i_1067_, v_acc_1068_);
lean_dec_ref(v_vals_1065_);
lean_dec_ref(v_keys_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_1070_, lean_object* v_opt_1071_){
_start:
{
lean_object* v_name_1072_; lean_object* v_defValue_1073_; lean_object* v_map_1074_; lean_object* v___x_1075_; 
v_name_1072_ = lean_ctor_get(v_opt_1071_, 0);
v_defValue_1073_ = lean_ctor_get(v_opt_1071_, 1);
v_map_1074_ = lean_ctor_get(v_opts_1070_, 0);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1074_, v_name_1072_);
if (lean_obj_tag(v___x_1075_) == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_unbox(v_defValue_1073_);
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; 
v_val_1077_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v___x_1075_);
if (lean_obj_tag(v_val_1077_) == 1)
{
uint8_t v_v_1078_; 
v_v_1078_ = lean_ctor_get_uint8(v_val_1077_, 0);
lean_dec_ref(v_val_1077_);
return v_v_1078_;
}
else
{
uint8_t v___x_1079_; 
lean_dec(v_val_1077_);
v___x_1079_ = lean_unbox(v_defValue_1073_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_1080_, lean_object* v_opt_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_1080_, v_opt_1081_);
lean_dec_ref(v_opt_1081_);
lean_dec_ref(v_opts_1080_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object* v_opts_1084_, lean_object* v_opt_1085_){
_start:
{
lean_object* v_name_1086_; lean_object* v_defValue_1087_; lean_object* v_map_1088_; lean_object* v___x_1089_; 
v_name_1086_ = lean_ctor_get(v_opt_1085_, 0);
v_defValue_1087_ = lean_ctor_get(v_opt_1085_, 1);
v_map_1088_ = lean_ctor_get(v_opts_1084_, 0);
v___x_1089_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1088_, v_name_1086_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_inc(v_defValue_1087_);
return v_defValue_1087_;
}
else
{
lean_object* v_val_1090_; 
v_val_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_val_1090_);
lean_dec_ref(v___x_1089_);
if (lean_obj_tag(v_val_1090_) == 3)
{
lean_object* v_v_1091_; 
v_v_1091_ = lean_ctor_get(v_val_1090_, 0);
lean_inc(v_v_1091_);
lean_dec_ref(v_val_1090_);
return v_v_1091_;
}
else
{
lean_dec(v_val_1090_);
lean_inc(v_defValue_1087_);
return v_defValue_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object* v_opts_1092_, lean_object* v_opt_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_opts_1092_, v_opt_1093_);
lean_dec_ref(v_opt_1093_);
lean_dec_ref(v_opts_1092_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_unsigned_to_nat(32u);
v___x_1096_ = lean_mk_empty_array_with_capacity(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
size_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_unsigned_to_nat(32u);
v___x_1101_ = lean_mk_empty_array_with_capacity(v___x_1100_);
v___x_1102_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0);
v___x_1103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1101_);
lean_ctor_set(v___x_1103_, 2, v___x_1099_);
lean_ctor_set(v___x_1103_, 3, v___x_1099_);
lean_ctor_set_usize(v___x_1103_, 4, v___x_1098_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_NameSet_empty;
v___x_1110_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_ctor_set(v___x_1111_, 2, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = l_Lean_firstFrontendMacroScope;
v___x_1114_ = lean_nat_add(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_1119_; uint64_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1120_ = 0ULL;
v___x_1121_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set_uint64(v___x_1121_, sizeof(void*)*1, v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_1123_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_1124_ = 1;
v___x_1125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1123_);
lean_ctor_set(v___x_1125_, 2, v___x_1122_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*3, v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l_Lean_Options_empty;
v___x_1131_ = l_Lean_Core_getMaxHeartbeats(v___x_1130_);
return v___x_1131_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = l_Lean_diagnostics;
v___x_1133_ = l_Lean_Options_empty;
v___x_1134_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = l_Lean_maxRecDepth;
v___x_1136_ = l_Lean_Options_empty;
v___x_1137_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_toCommandContextInfo_1145_; lean_object* v_env_1146_; lean_object* v_options_1147_; lean_object* v_currNamespace_1148_; lean_object* v_openDecls_1149_; lean_object* v_ngen_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v_env_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v_fileName_1165_; lean_object* v_fileMap_1166_; lean_object* v_currRecDepth_1167_; lean_object* v_ref_1168_; lean_object* v_currNamespace_1169_; lean_object* v_openDecls_1170_; lean_object* v_initHeartbeats_1171_; lean_object* v_maxHeartbeats_1172_; lean_object* v_quotContext_1173_; lean_object* v_currMacroScope_1174_; lean_object* v_cancelTk_x3f_1175_; uint8_t v_suppressElabErrors_1176_; lean_object* v_inheritedTraceOptions_1177_; lean_object* v___y_1178_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1233_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_env_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v___y_1299_; uint8_t v___x_1319_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_1143_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_1144_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_1145_ = lean_ctor_get(v_info_1138_, 0);
lean_inc_ref(v_toCommandContextInfo_1145_);
lean_dec_ref(v_info_1138_);
v_env_1146_ = lean_ctor_get(v_toCommandContextInfo_1145_, 0);
lean_inc_ref(v_env_1146_);
v_options_1147_ = lean_ctor_get(v_toCommandContextInfo_1145_, 4);
lean_inc_ref(v_options_1147_);
v_currNamespace_1148_ = lean_ctor_get(v_toCommandContextInfo_1145_, 5);
lean_inc(v_currNamespace_1148_);
v_openDecls_1149_ = lean_ctor_get(v_toCommandContextInfo_1145_, 6);
lean_inc(v_openDecls_1149_);
v_ngen_1150_ = lean_ctor_get(v_toCommandContextInfo_1145_, 7);
lean_inc_ref(v_ngen_1150_);
lean_dec_ref(v_toCommandContextInfo_1145_);
v___x_1151_ = l_Lean_firstFrontendMacroScope;
v___x_1152_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_1153_ = 0;
v_env_1154_ = l_Lean_Environment_setExporting(v_env_1146_, v___x_1153_);
v___x_1155_ = lean_box(0);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7));
v___x_1157_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_1160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1160_, 0, v_env_1154_);
lean_ctor_set(v___x_1160_, 1, v___x_1152_);
lean_ctor_set(v___x_1160_, 2, v_ngen_1150_);
lean_ctor_set(v___x_1160_, 3, v___x_1156_);
lean_ctor_set(v___x_1160_, 4, v___x_1157_);
lean_ctor_set(v___x_1160_, 5, v___x_1142_);
lean_ctor_set(v___x_1160_, 6, v___x_1143_);
lean_ctor_set(v___x_1160_, 7, v___x_1158_);
lean_ctor_set(v___x_1160_, 8, v___x_1159_);
v___x_1161_ = lean_st_mk_ref(v___x_1160_);
v___x_1253_ = l_Lean_inheritedTraceOptions;
v___x_1254_ = lean_st_ref_get(v___x_1253_);
v___x_1255_ = lean_st_ref_get(v___x_1161_);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_1257_ = l_Lean_instInhabitedFileMap_default;
v___x_1258_ = l_Lean_Options_empty;
v___x_1259_ = lean_unsigned_to_nat(1000u);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1263_, 0, v___x_1256_);
lean_ctor_set(v___x_1263_, 1, v___x_1257_);
lean_ctor_set(v___x_1263_, 2, v___x_1258_);
lean_ctor_set(v___x_1263_, 3, v___x_1141_);
lean_ctor_set(v___x_1263_, 4, v___x_1259_);
lean_ctor_set(v___x_1263_, 5, v___x_1260_);
lean_ctor_set(v___x_1263_, 6, v_currNamespace_1148_);
lean_ctor_set(v___x_1263_, 7, v_openDecls_1149_);
lean_ctor_set(v___x_1263_, 8, v___x_1144_);
lean_ctor_set(v___x_1263_, 9, v___x_1261_);
lean_ctor_set(v___x_1263_, 10, v___x_1155_);
lean_ctor_set(v___x_1263_, 11, v___x_1151_);
lean_ctor_set(v___x_1263_, 12, v___x_1262_);
lean_ctor_set(v___x_1263_, 13, v___x_1254_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*14, v___x_1153_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*14 + 1, v___x_1153_);
v_env_1264_ = lean_ctor_get(v___x_1255_, 0);
lean_inc_ref(v_env_1264_);
lean_dec(v___x_1255_);
v___x_1265_ = l_Lean_diagnostics;
v___x_1266_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_1319_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1264_);
lean_dec_ref(v_env_1264_);
if (v___x_1319_ == 0)
{
if (v___x_1266_ == 0)
{
lean_inc(v___x_1161_);
v___y_1268_ = v___x_1263_;
v___y_1269_ = v___x_1161_;
goto v___jp_1267_;
}
else
{
v___y_1299_ = v___x_1319_;
goto v___jp_1298_;
}
}
else
{
v___y_1299_ = v___x_1266_;
goto v___jp_1298_;
}
v___jp_1162_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_1147_, v___y_1164_);
lean_dec_ref(v___y_1164_);
v___x_1180_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1180_, 0, v_fileName_1165_);
lean_ctor_set(v___x_1180_, 1, v_fileMap_1166_);
lean_ctor_set(v___x_1180_, 2, v_options_1147_);
lean_ctor_set(v___x_1180_, 3, v_currRecDepth_1167_);
lean_ctor_set(v___x_1180_, 4, v___x_1179_);
lean_ctor_set(v___x_1180_, 5, v_ref_1168_);
lean_ctor_set(v___x_1180_, 6, v_currNamespace_1169_);
lean_ctor_set(v___x_1180_, 7, v_openDecls_1170_);
lean_ctor_set(v___x_1180_, 8, v_initHeartbeats_1171_);
lean_ctor_set(v___x_1180_, 9, v_maxHeartbeats_1172_);
lean_ctor_set(v___x_1180_, 10, v_quotContext_1173_);
lean_ctor_set(v___x_1180_, 11, v_currMacroScope_1174_);
lean_ctor_set(v___x_1180_, 12, v_cancelTk_x3f_1175_);
lean_ctor_set(v___x_1180_, 13, v_inheritedTraceOptions_1177_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*14, v___y_1163_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*14 + 1, v_suppressElabErrors_1176_);
v___x_1181_ = lean_apply_3(v_x_1139_, v___x_1180_, v___y_1178_, lean_box(0));
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1190_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_st_ref_get(v___x_1161_);
lean_dec(v___x_1161_);
lean_dec(v___x_1186_);
if (v_isShared_1185_ == 0)
{
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1182_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v___x_1161_);
v_a_1191_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1193_ = v___x_1181_;
v_isShared_1194_ = v_isSharedCheck_1209_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1181_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1209_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
if (lean_obj_tag(v_a_1191_) == 0)
{
lean_object* v_msg_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_msg_1195_ = lean_ctor_get(v_a_1191_, 1);
lean_inc_ref(v_msg_1195_);
lean_dec_ref(v_a_1191_);
v___x_1196_ = l_Lean_MessageData_toString(v_msg_1195_);
v___x_1197_ = lean_mk_io_user_error(v___x_1196_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1199_ = v___x_1193_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v_id_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v_id_1201_ = lean_ctor_get(v_a_1191_, 0);
lean_inc(v_id_1201_);
lean_dec_ref(v_a_1191_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_1203_ = l_Nat_reprFast(v_id_1201_);
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = lean_mk_io_user_error(v___x_1204_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1205_);
v___x_1207_ = v___x_1193_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
v___jp_1210_:
{
lean_object* v_fileName_1215_; lean_object* v_fileMap_1216_; lean_object* v_currRecDepth_1217_; lean_object* v_ref_1218_; lean_object* v_currNamespace_1219_; lean_object* v_openDecls_1220_; lean_object* v_initHeartbeats_1221_; lean_object* v_maxHeartbeats_1222_; lean_object* v_quotContext_1223_; lean_object* v_currMacroScope_1224_; lean_object* v_cancelTk_x3f_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_inheritedTraceOptions_1227_; 
v_fileName_1215_ = lean_ctor_get(v___y_1213_, 0);
lean_inc_ref(v_fileName_1215_);
v_fileMap_1216_ = lean_ctor_get(v___y_1213_, 1);
lean_inc_ref(v_fileMap_1216_);
v_currRecDepth_1217_ = lean_ctor_get(v___y_1213_, 3);
lean_inc(v_currRecDepth_1217_);
v_ref_1218_ = lean_ctor_get(v___y_1213_, 5);
lean_inc(v_ref_1218_);
v_currNamespace_1219_ = lean_ctor_get(v___y_1213_, 6);
lean_inc(v_currNamespace_1219_);
v_openDecls_1220_ = lean_ctor_get(v___y_1213_, 7);
lean_inc(v_openDecls_1220_);
v_initHeartbeats_1221_ = lean_ctor_get(v___y_1213_, 8);
lean_inc(v_initHeartbeats_1221_);
v_maxHeartbeats_1222_ = lean_ctor_get(v___y_1213_, 9);
lean_inc(v_maxHeartbeats_1222_);
v_quotContext_1223_ = lean_ctor_get(v___y_1213_, 10);
lean_inc(v_quotContext_1223_);
v_currMacroScope_1224_ = lean_ctor_get(v___y_1213_, 11);
lean_inc(v_currMacroScope_1224_);
v_cancelTk_x3f_1225_ = lean_ctor_get(v___y_1213_, 12);
lean_inc(v_cancelTk_x3f_1225_);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1213_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1227_ = lean_ctor_get(v___y_1213_, 13);
lean_inc_ref(v_inheritedTraceOptions_1227_);
lean_dec_ref(v___y_1213_);
v___y_1163_ = v___y_1211_;
v___y_1164_ = v___y_1212_;
v_fileName_1165_ = v_fileName_1215_;
v_fileMap_1166_ = v_fileMap_1216_;
v_currRecDepth_1167_ = v_currRecDepth_1217_;
v_ref_1168_ = v_ref_1218_;
v_currNamespace_1169_ = v_currNamespace_1219_;
v_openDecls_1170_ = v_openDecls_1220_;
v_initHeartbeats_1171_ = v_initHeartbeats_1221_;
v_maxHeartbeats_1172_ = v_maxHeartbeats_1222_;
v_quotContext_1173_ = v_quotContext_1223_;
v_currMacroScope_1174_ = v_currMacroScope_1224_;
v_cancelTk_x3f_1175_ = v_cancelTk_x3f_1225_;
v_suppressElabErrors_1176_ = v_suppressElabErrors_1226_;
v_inheritedTraceOptions_1177_ = v_inheritedTraceOptions_1227_;
v___y_1178_ = v___y_1214_;
goto v___jp_1162_;
}
v___jp_1228_:
{
if (v___y_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v_env_1235_; lean_object* v_nextMacroScope_1236_; lean_object* v_ngen_1237_; lean_object* v_auxDeclNGen_1238_; lean_object* v_traceState_1239_; lean_object* v_messages_1240_; lean_object* v_infoState_1241_; lean_object* v_snapshotTasks_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1251_; 
v___x_1234_ = lean_st_ref_take(v___y_1232_);
v_env_1235_ = lean_ctor_get(v___x_1234_, 0);
v_nextMacroScope_1236_ = lean_ctor_get(v___x_1234_, 1);
v_ngen_1237_ = lean_ctor_get(v___x_1234_, 2);
v_auxDeclNGen_1238_ = lean_ctor_get(v___x_1234_, 3);
v_traceState_1239_ = lean_ctor_get(v___x_1234_, 4);
v_messages_1240_ = lean_ctor_get(v___x_1234_, 6);
v_infoState_1241_ = lean_ctor_get(v___x_1234_, 7);
v_snapshotTasks_1242_ = lean_ctor_get(v___x_1234_, 8);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1234_, 5);
lean_dec(v_unused_1252_);
v___x_1244_ = v___x_1234_;
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snapshotTasks_1242_);
lean_inc(v_infoState_1241_);
lean_inc(v_messages_1240_);
lean_inc(v_traceState_1239_);
lean_inc(v_auxDeclNGen_1238_);
lean_inc(v_ngen_1237_);
lean_inc(v_nextMacroScope_1236_);
lean_inc(v_env_1235_);
lean_dec(v___x_1234_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_Kernel_enableDiag(v_env_1235_, v___y_1229_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 5, v___x_1142_);
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_nextMacroScope_1236_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_ngen_1237_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_auxDeclNGen_1238_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_traceState_1239_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_messages_1240_);
lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_infoState_1241_);
lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_snapshotTasks_1242_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_st_ref_set(v___y_1232_, v___x_1248_);
v___y_1211_ = v___y_1229_;
v___y_1212_ = v___y_1231_;
v___y_1213_ = v___y_1230_;
v___y_1214_ = v___y_1232_;
goto v___jp_1210_;
}
}
}
else
{
v___y_1211_ = v___y_1229_;
v___y_1212_ = v___y_1231_;
v___y_1213_ = v___y_1230_;
v___y_1214_ = v___y_1232_;
goto v___jp_1210_;
}
}
v___jp_1267_:
{
lean_object* v___x_1270_; lean_object* v_fileName_1271_; lean_object* v_fileMap_1272_; lean_object* v_currRecDepth_1273_; lean_object* v_ref_1274_; lean_object* v_currNamespace_1275_; lean_object* v_openDecls_1276_; lean_object* v_initHeartbeats_1277_; lean_object* v_maxHeartbeats_1278_; lean_object* v_quotContext_1279_; lean_object* v_currMacroScope_1280_; lean_object* v_cancelTk_x3f_1281_; uint8_t v_suppressElabErrors_1282_; lean_object* v_inheritedTraceOptions_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1295_; 
v___x_1270_ = lean_st_ref_get(v___y_1269_);
v_fileName_1271_ = lean_ctor_get(v___y_1268_, 0);
v_fileMap_1272_ = lean_ctor_get(v___y_1268_, 1);
v_currRecDepth_1273_ = lean_ctor_get(v___y_1268_, 3);
v_ref_1274_ = lean_ctor_get(v___y_1268_, 5);
v_currNamespace_1275_ = lean_ctor_get(v___y_1268_, 6);
v_openDecls_1276_ = lean_ctor_get(v___y_1268_, 7);
v_initHeartbeats_1277_ = lean_ctor_get(v___y_1268_, 8);
v_maxHeartbeats_1278_ = lean_ctor_get(v___y_1268_, 9);
v_quotContext_1279_ = lean_ctor_get(v___y_1268_, 10);
v_currMacroScope_1280_ = lean_ctor_get(v___y_1268_, 11);
v_cancelTk_x3f_1281_ = lean_ctor_get(v___y_1268_, 12);
v_suppressElabErrors_1282_ = lean_ctor_get_uint8(v___y_1268_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1283_ = lean_ctor_get(v___y_1268_, 13);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1268_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1296_ = lean_ctor_get(v___y_1268_, 4);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v___y_1268_, 2);
lean_dec(v_unused_1297_);
v___x_1285_ = v___y_1268_;
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_inheritedTraceOptions_1283_);
lean_inc(v_cancelTk_x3f_1281_);
lean_inc(v_currMacroScope_1280_);
lean_inc(v_quotContext_1279_);
lean_inc(v_maxHeartbeats_1278_);
lean_inc(v_initHeartbeats_1277_);
lean_inc(v_openDecls_1276_);
lean_inc(v_currNamespace_1275_);
lean_inc(v_ref_1274_);
lean_inc(v_currRecDepth_1273_);
lean_inc(v_fileMap_1272_);
lean_inc(v_fileName_1271_);
lean_dec(v___y_1268_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_env_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v_env_1287_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_env_1287_);
lean_dec(v___x_1270_);
v___x_1288_ = l_Lean_maxRecDepth;
v___x_1289_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
lean_inc_ref(v_inheritedTraceOptions_1283_);
lean_inc(v_cancelTk_x3f_1281_);
lean_inc(v_currMacroScope_1280_);
lean_inc(v_quotContext_1279_);
lean_inc(v_maxHeartbeats_1278_);
lean_inc(v_initHeartbeats_1277_);
lean_inc(v_openDecls_1276_);
lean_inc(v_currNamespace_1275_);
lean_inc(v_ref_1274_);
lean_inc(v_currRecDepth_1273_);
lean_inc_ref(v_fileMap_1272_);
lean_inc_ref(v_fileName_1271_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1289_);
lean_ctor_set(v___x_1285_, 2, v___x_1258_);
v___x_1291_ = v___x_1285_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fileName_1271_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_fileMap_1272_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_currRecDepth_1273_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v_ref_1274_);
lean_ctor_set(v_reuseFailAlloc_1294_, 6, v_currNamespace_1275_);
lean_ctor_set(v_reuseFailAlloc_1294_, 7, v_openDecls_1276_);
lean_ctor_set(v_reuseFailAlloc_1294_, 8, v_initHeartbeats_1277_);
lean_ctor_set(v_reuseFailAlloc_1294_, 9, v_maxHeartbeats_1278_);
lean_ctor_set(v_reuseFailAlloc_1294_, 10, v_quotContext_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 11, v_currMacroScope_1280_);
lean_ctor_set(v_reuseFailAlloc_1294_, 12, v_cancelTk_x3f_1281_);
lean_ctor_set(v_reuseFailAlloc_1294_, 13, v_inheritedTraceOptions_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*14 + 1, v_suppressElabErrors_1282_);
v___x_1291_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
uint8_t v___x_1292_; uint8_t v___x_1293_; 
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*14, v___x_1266_);
v___x_1292_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_1147_, v___x_1265_);
v___x_1293_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1287_);
lean_dec_ref(v_env_1287_);
if (v___x_1293_ == 0)
{
if (v___x_1292_ == 0)
{
lean_dec_ref(v___x_1291_);
v___y_1163_ = v___x_1292_;
v___y_1164_ = v___x_1288_;
v_fileName_1165_ = v_fileName_1271_;
v_fileMap_1166_ = v_fileMap_1272_;
v_currRecDepth_1167_ = v_currRecDepth_1273_;
v_ref_1168_ = v_ref_1274_;
v_currNamespace_1169_ = v_currNamespace_1275_;
v_openDecls_1170_ = v_openDecls_1276_;
v_initHeartbeats_1171_ = v_initHeartbeats_1277_;
v_maxHeartbeats_1172_ = v_maxHeartbeats_1278_;
v_quotContext_1173_ = v_quotContext_1279_;
v_currMacroScope_1174_ = v_currMacroScope_1280_;
v_cancelTk_x3f_1175_ = v_cancelTk_x3f_1281_;
v_suppressElabErrors_1176_ = v_suppressElabErrors_1282_;
v_inheritedTraceOptions_1177_ = v_inheritedTraceOptions_1283_;
v___y_1178_ = v___y_1269_;
goto v___jp_1162_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1283_);
lean_dec(v_cancelTk_x3f_1281_);
lean_dec(v_currMacroScope_1280_);
lean_dec(v_quotContext_1279_);
lean_dec(v_maxHeartbeats_1278_);
lean_dec(v_initHeartbeats_1277_);
lean_dec(v_openDecls_1276_);
lean_dec(v_currNamespace_1275_);
lean_dec(v_ref_1274_);
lean_dec(v_currRecDepth_1273_);
lean_dec_ref(v_fileMap_1272_);
lean_dec_ref(v_fileName_1271_);
v___y_1229_ = v___x_1292_;
v___y_1230_ = v___x_1291_;
v___y_1231_ = v___x_1288_;
v___y_1232_ = v___y_1269_;
v___y_1233_ = v___x_1293_;
goto v___jp_1228_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_1283_);
lean_dec(v_cancelTk_x3f_1281_);
lean_dec(v_currMacroScope_1280_);
lean_dec(v_quotContext_1279_);
lean_dec(v_maxHeartbeats_1278_);
lean_dec(v_initHeartbeats_1277_);
lean_dec(v_openDecls_1276_);
lean_dec(v_currNamespace_1275_);
lean_dec(v_ref_1274_);
lean_dec(v_currRecDepth_1273_);
lean_dec_ref(v_fileMap_1272_);
lean_dec_ref(v_fileName_1271_);
v___y_1229_ = v___x_1292_;
v___y_1230_ = v___x_1291_;
v___y_1231_ = v___x_1288_;
v___y_1232_ = v___y_1269_;
v___y_1233_ = v___x_1292_;
goto v___jp_1228_;
}
}
}
}
v___jp_1298_:
{
if (v___y_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v_env_1301_; lean_object* v_nextMacroScope_1302_; lean_object* v_ngen_1303_; lean_object* v_auxDeclNGen_1304_; lean_object* v_traceState_1305_; lean_object* v_messages_1306_; lean_object* v_infoState_1307_; lean_object* v_snapshotTasks_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
v___x_1300_ = lean_st_ref_take(v___x_1161_);
v_env_1301_ = lean_ctor_get(v___x_1300_, 0);
v_nextMacroScope_1302_ = lean_ctor_get(v___x_1300_, 1);
v_ngen_1303_ = lean_ctor_get(v___x_1300_, 2);
v_auxDeclNGen_1304_ = lean_ctor_get(v___x_1300_, 3);
v_traceState_1305_ = lean_ctor_get(v___x_1300_, 4);
v_messages_1306_ = lean_ctor_get(v___x_1300_, 6);
v_infoState_1307_ = lean_ctor_get(v___x_1300_, 7);
v_snapshotTasks_1308_ = lean_ctor_get(v___x_1300_, 8);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1300_, 5);
lean_dec(v_unused_1318_);
v___x_1310_ = v___x_1300_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snapshotTasks_1308_);
lean_inc(v_infoState_1307_);
lean_inc(v_messages_1306_);
lean_inc(v_traceState_1305_);
lean_inc(v_auxDeclNGen_1304_);
lean_inc(v_ngen_1303_);
lean_inc(v_nextMacroScope_1302_);
lean_inc(v_env_1301_);
lean_dec(v___x_1300_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_Kernel_enableDiag(v_env_1301_, v___x_1266_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 5, v___x_1142_);
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_nextMacroScope_1302_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_ngen_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_auxDeclNGen_1304_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_traceState_1305_);
lean_ctor_set(v_reuseFailAlloc_1316_, 5, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1316_, 6, v_messages_1306_);
lean_ctor_set(v_reuseFailAlloc_1316_, 7, v_infoState_1307_);
lean_ctor_set(v_reuseFailAlloc_1316_, 8, v_snapshotTasks_1308_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_st_ref_set(v___x_1161_, v___x_1314_);
lean_inc(v___x_1161_);
v___y_1268_ = v___x_1263_;
v___y_1269_ = v___x_1161_;
goto v___jp_1267_;
}
}
}
else
{
lean_inc(v___x_1161_);
v___y_1268_ = v___x_1263_;
v___y_1269_ = v___x_1161_;
goto v___jp_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_1320_, lean_object* v_x_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1320_, v_x_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_1324_, lean_object* v_info_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1325_, v_x_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_info_1330_, lean_object* v_x_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_1329_, v_info_1330_, v_x_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_1334_, lean_object* v_x_1335_, lean_object* v___x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_st_mk_ref(v___x_1334_);
lean_inc(v___x_1340_);
v___x_1341_ = lean_apply_5(v_x_1335_, v___x_1336_, v___x_1340_, v___y_1337_, v___y_1338_, lean_box(0));
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1351_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = lean_st_ref_get(v___x_1340_);
lean_dec(v___x_1340_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1342_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v___x_1340_);
v_a_1352_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1341_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1341_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_1360_, lean_object* v_x_1361_, lean_object* v___x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_1360_, v_x_1361_, v___x_1362_, v___y_1363_, v___y_1364_);
return v_res_1366_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1369_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1373_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
lean_ctor_set(v___x_1373_, 3, v___x_1372_);
lean_ctor_set(v___x_1373_, 4, v___x_1372_);
lean_ctor_set(v___x_1373_, 5, v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_unsigned_to_nat(32u);
v___x_1375_ = lean_mk_empty_array_with_capacity(v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
size_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1377_ = ((size_t)5ULL);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_unsigned_to_nat(32u);
v___x_1380_ = lean_mk_empty_array_with_capacity(v___x_1379_);
v___x_1381_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_1382_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
lean_ctor_set(v___x_1382_, 2, v___x_1378_);
lean_ctor_set(v___x_1382_, 3, v___x_1378_);
lean_ctor_set_usize(v___x_1382_, 4, v___x_1377_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
lean_ctor_set(v___x_1384_, 3, v___x_1383_);
lean_ctor_set(v___x_1384_, 4, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_1385_, lean_object* v_lctx_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v_toCommandContextInfo_1397_; lean_object* v_mctx_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___x_1389_ = lean_box(1);
v___x_1390_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_1391_ = 0;
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_1394_ = lean_box(0);
v___x_1395_ = 1;
v___x_1396_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1396_, 0, v___x_1390_);
lean_ctor_set(v___x_1396_, 1, v___x_1389_);
lean_ctor_set(v___x_1396_, 2, v_lctx_1386_);
lean_ctor_set(v___x_1396_, 3, v___x_1393_);
lean_ctor_set(v___x_1396_, 4, v___x_1394_);
lean_ctor_set(v___x_1396_, 5, v___x_1392_);
lean_ctor_set(v___x_1396_, 6, v___x_1394_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*7, v___x_1391_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*7 + 1, v___x_1391_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*7 + 2, v___x_1391_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*7 + 3, v___x_1395_);
v_toCommandContextInfo_1397_ = lean_ctor_get(v_info_1385_, 0);
v_mctx_1398_ = lean_ctor_get(v_toCommandContextInfo_1397_, 3);
v___x_1399_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3);
v___x_1400_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_1401_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
lean_inc_ref(v_mctx_1398_);
v___x_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1402_, 0, v_mctx_1398_);
lean_ctor_set(v___x_1402_, 1, v___x_1399_);
lean_ctor_set(v___x_1402_, 2, v___x_1389_);
lean_ctor_set(v___x_1402_, 3, v___x_1400_);
lean_ctor_set(v___x_1402_, 4, v___x_1401_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1403_, 0, v___x_1402_);
lean_closure_set(v___f_1403_, 1, v_x_1387_);
lean_closure_set(v___f_1403_, 2, v___x_1396_);
v___x_1404_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_1385_, v___f_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_fst_1409_; lean_object* v___x_1411_; 
v_fst_1409_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1409_);
lean_dec(v_a_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v_fst_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_fst_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1404_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1404_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_1422_, lean_object* v_lctx_1423_, lean_object* v_x_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1422_, v_lctx_1423_, v_x_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_1427_, lean_object* v_info_1428_, lean_object* v_lctx_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_1428_, v_lctx_1429_, v_x_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_info_1434_, lean_object* v_lctx_1435_, lean_object* v_x_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_1433_, v_info_1434_, v_lctx_1435_, v_x_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_1439_, lean_object* v_lctx_1440_){
_start:
{
lean_object* v_toCommandContextInfo_1441_; lean_object* v_env_1442_; lean_object* v_mctx_1443_; lean_object* v_options_1444_; lean_object* v_currNamespace_1445_; lean_object* v_openDecls_1446_; lean_object* v___x_1447_; 
v_toCommandContextInfo_1441_ = lean_ctor_get(v_info_1439_, 0);
v_env_1442_ = lean_ctor_get(v_toCommandContextInfo_1441_, 0);
v_mctx_1443_ = lean_ctor_get(v_toCommandContextInfo_1441_, 3);
v_options_1444_ = lean_ctor_get(v_toCommandContextInfo_1441_, 4);
v_currNamespace_1445_ = lean_ctor_get(v_toCommandContextInfo_1441_, 5);
v_openDecls_1446_ = lean_ctor_get(v_toCommandContextInfo_1441_, 6);
lean_inc(v_openDecls_1446_);
lean_inc(v_currNamespace_1445_);
lean_inc_ref(v_options_1444_);
lean_inc_ref(v_mctx_1443_);
lean_inc_ref(v_env_1442_);
v___x_1447_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1447_, 0, v_env_1442_);
lean_ctor_set(v___x_1447_, 1, v_mctx_1443_);
lean_ctor_set(v___x_1447_, 2, v_lctx_1440_);
lean_ctor_set(v___x_1447_, 3, v_options_1444_);
lean_ctor_set(v___x_1447_, 4, v_currNamespace_1445_);
lean_ctor_set(v___x_1447_, 5, v_openDecls_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_1448_, lean_object* v_lctx_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1448_, v_lctx_1449_);
lean_dec_ref(v_info_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_1451_, lean_object* v_lctx_1452_, lean_object* v_stx_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_1451_, v_lctx_1452_);
v___x_1456_ = l_Lean_ppTerm(v___x_1455_, v_stx_1453_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_1458_, lean_object* v_lctx_1459_, lean_object* v_stx_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_1458_, v_lctx_1459_, v_stx_1460_);
lean_dec_ref(v_info_1458_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_1478_, lean_object* v_pos_1479_, lean_object* v_info_1480_){
_start:
{
lean_object* v_toCommandContextInfo_1481_; lean_object* v_fileMap_1482_; lean_object* v___x_1483_; lean_object* v_line_1484_; lean_object* v_column_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1508_; 
v_toCommandContextInfo_1481_ = lean_ctor_get(v_ctx_1478_, 0);
lean_inc_ref(v_toCommandContextInfo_1481_);
lean_dec_ref(v_ctx_1478_);
v_fileMap_1482_ = lean_ctor_get(v_toCommandContextInfo_1481_, 2);
lean_inc_ref(v_fileMap_1482_);
lean_dec_ref(v_toCommandContextInfo_1481_);
v___x_1483_ = l_Lean_FileMap_toPosition(v_fileMap_1482_, v_pos_1479_);
v_line_1484_ = lean_ctor_get(v___x_1483_, 0);
v_column_1485_ = lean_ctor_get(v___x_1483_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1487_ = v___x_1483_;
v_isShared_1488_ = v_isSharedCheck_1508_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_column_1485_);
lean_inc(v_line_1484_);
lean_dec(v___x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1508_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1490_ = l_Nat_reprFast(v_line_1484_);
v___x_1491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 5);
lean_ctor_set(v___x_1487_, 1, v___x_1491_);
lean_ctor_set(v___x_1487_, 0, v___x_1489_);
v___x_1493_ = v___x_1487_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_pos_1500_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_1495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Nat_reprFast(v_column_1485_);
v___x_1497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
v___x_1498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1495_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_1500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_1500_, 0, v___x_1498_);
lean_ctor_set(v_pos_1500_, 1, v___x_1499_);
switch(lean_obj_tag(v_info_1480_))
{
case 0:
{
return v_pos_1500_;
}
case 1:
{
uint8_t v_canonical_1504_; 
v_canonical_1504_ = lean_ctor_get_uint8(v_info_1480_, sizeof(void*)*2);
if (v_canonical_1504_ == 1)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_1506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_pos_1500_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
return v___x_1506_;
}
else
{
goto v___jp_1501_;
}
}
default: 
{
goto v___jp_1501_;
}
}
v___jp_1501_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_1503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_pos_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_1509_, lean_object* v_pos_1510_, lean_object* v_info_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1509_, v_pos_1510_, v_info_1511_);
lean_dec(v_info_1511_);
lean_dec(v_pos_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_1516_, lean_object* v_stx_1517_){
_start:
{
lean_object* v___y_1519_; lean_object* v___y_1520_; uint8_t v___x_1528_; lean_object* v___y_1530_; lean_object* v___x_1533_; 
v___x_1528_ = 0;
v___x_1533_ = l_Lean_Syntax_getPos_x3f(v_stx_1517_, v___x_1528_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___y_1530_ = v___x_1534_;
goto v___jp_1529_;
}
else
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1535_);
lean_dec_ref(v___x_1533_);
v___y_1530_ = v_val_1535_;
goto v___jp_1529_;
}
v___jp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1521_ = l_Lean_Syntax_getHeadInfo(v_stx_1517_);
lean_inc_ref(v_ctx_1516_);
v___x_1522_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1516_, v___y_1519_, v___x_1521_);
lean_dec(v___x_1521_);
lean_dec(v___y_1519_);
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_Syntax_getTailInfo(v_stx_1517_);
v___x_1526_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_1516_, v___y_1520_, v___x_1525_);
lean_dec(v___x_1525_);
lean_dec(v___y_1520_);
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1524_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
return v___x_1527_;
}
v___jp_1529_:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1517_, v___x_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_inc(v___y_1530_);
v___y_1519_ = v___y_1530_;
v___y_1520_ = v___y_1530_;
goto v___jp_1518_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v___x_1531_);
v___y_1519_ = v___y_1530_;
v___y_1520_ = v_val_1532_;
goto v___jp_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_1536_, lean_object* v_stx_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1536_, v_stx_1537_);
lean_dec(v_stx_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_1542_, lean_object* v_info_1543_){
_start:
{
lean_object* v_elaborator_1544_; lean_object* v_stx_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1560_; 
v_elaborator_1544_ = lean_ctor_get(v_info_1543_, 0);
v_stx_1545_ = lean_ctor_get(v_info_1543_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_info_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1547_ = v_info_1543_;
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_stx_1545_);
lean_inc(v_elaborator_1544_);
lean_dec(v_info_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lean_Name_isAnonymous(v_elaborator_1544_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1550_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1542_, v_stx_1545_);
lean_dec(v_stx_1545_);
v___x_1551_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 5);
lean_ctor_set(v___x_1547_, 1, v___x_1551_);
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1553_ = v___x_1547_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = 1;
v___x_1555_ = l_Lean_Name_toString(v_elaborator_1544_, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1553_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
return v___x_1557_;
}
}
else
{
lean_object* v___x_1559_; 
lean_del_object(v___x_1547_);
lean_dec(v_elaborator_1544_);
v___x_1559_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1542_, v_stx_1545_);
lean_dec(v_stx_1545_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_1561_, lean_object* v_ctx_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v_lctx_1565_; lean_object* v___x_1566_; 
v_lctx_1565_ = lean_ctor_get(v_info_1561_, 1);
lean_inc_ref(v_lctx_1565_);
lean_dec_ref(v_info_1561_);
v___x_1566_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1562_, v_lctx_1565_, v_x_1563_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_1567_, lean_object* v_ctx_1568_, lean_object* v_x_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1567_, v_ctx_1568_, v_x_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_1572_, lean_object* v_info_1573_, lean_object* v_ctx_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1573_, v_ctx_1574_, v_x_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_info_1579_, lean_object* v_ctx_1580_, lean_object* v_x_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_1578_, v_info_1579_, v_ctx_1580_, v_x_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_1598_, lean_object* v_toElabInfo_1599_, lean_object* v_expr_1600_, uint8_t v_isBinder_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v_a_1622_; lean_object* v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1636_; lean_object* v_a_1637_; lean_object* v___x_1640_; 
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc_ref(v_expr_1600_);
v___x_1640_ = lean_infer_type(v_expr_1600_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = l_Lean_Meta_ppExpr(v_a_1641_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
v_a_1622_ = v_a_1643_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1644_; 
v_a_1644_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1644_);
v___y_1636_ = v___x_1642_;
v_a_1637_ = v_a_1644_;
goto v___jp_1635_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1640_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1640_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
lean_inc(v_a_1645_);
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
v___y_1636_ = v___x_1650_;
v_a_1637_ = v_a_1645_;
goto v___jp_1635_;
}
}
}
v___jp_1607_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1610_);
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1609_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___y_1608_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1598_, v_toElabInfo_1599_);
v___x_1619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
v___jp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_ppExpr(v_expr_1600_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_a_1624_);
v___x_1627_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
if (v_isBinder_1601_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_1608_ = v_a_1622_;
v___y_1609_ = v___x_1628_;
v___y_1610_ = v___x_1629_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_1608_ = v_a_1622_;
v___y_1609_ = v___x_1628_;
v___y_1610_ = v___x_1630_;
goto v___jp_1607_;
}
}
else
{
lean_dec(v_a_1622_);
lean_dec_ref(v_toElabInfo_1599_);
lean_dec_ref(v_ctx_1598_);
return v___x_1623_;
}
}
v___jp_1631_:
{
if (v___y_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref(v___y_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_1622_ = v___x_1634_;
goto v___jp_1621_;
}
else
{
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_expr_1600_);
lean_dec_ref(v_toElabInfo_1599_);
lean_dec_ref(v_ctx_1598_);
return v___y_1632_;
}
}
v___jp_1635_:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Lean_Exception_isInterrupt(v_a_1637_);
if (v___x_1638_ == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = l_Lean_Exception_isRuntime(v_a_1637_);
v___y_1632_ = v___y_1636_;
v___y_1633_ = v___x_1639_;
goto v___jp_1631_;
}
else
{
lean_dec_ref(v_a_1637_);
v___y_1632_ = v___y_1636_;
v___y_1633_ = v___x_1638_;
goto v___jp_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_1653_, lean_object* v_toElabInfo_1654_, lean_object* v_expr_1655_, lean_object* v_isBinder_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_isBinder_boxed_1662_; lean_object* v_res_1663_; 
v_isBinder_boxed_1662_ = lean_unbox(v_isBinder_1656_);
v_res_1663_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_1653_, v_toElabInfo_1654_, v_expr_1655_, v_isBinder_boxed_1662_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_1664_, lean_object* v_info_1665_){
_start:
{
lean_object* v_toElabInfo_1667_; lean_object* v_expr_1668_; uint8_t v_isBinder_1669_; lean_object* v___x_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; 
v_toElabInfo_1667_ = lean_ctor_get(v_info_1665_, 0);
v_expr_1668_ = lean_ctor_get(v_info_1665_, 3);
v_isBinder_1669_ = lean_ctor_get_uint8(v_info_1665_, sizeof(void*)*4);
v___x_1670_ = lean_box(v_isBinder_1669_);
lean_inc_ref(v_expr_1668_);
lean_inc_ref(v_toElabInfo_1667_);
lean_inc_ref(v_ctx_1664_);
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1671_, 0, v_ctx_1664_);
lean_closure_set(v___f_1671_, 1, v_toElabInfo_1667_);
lean_closure_set(v___f_1671_, 2, v_expr_1668_);
lean_closure_set(v___f_1671_, 3, v___x_1670_);
v___x_1672_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_1665_, v_ctx_1664_, v___f_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_1673_, lean_object* v_info_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_TermInfo_format(v_ctx_1673_, v_info_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_1680_, lean_object* v_info_1681_){
_start:
{
lean_object* v_toElabInfo_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_toElabInfo_1682_ = lean_ctor_get(v_info_1681_, 0);
lean_inc_ref(v_toElabInfo_1682_);
lean_dec_ref(v_info_1681_);
v___x_1683_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_1684_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1680_, v_toElabInfo_1682_);
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1693_;
}
else
{
lean_object* v_val_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1704_; 
v_val_1694_ = lean_ctor_get(v_x_1692_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_x_1692_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1696_ = v_x_1692_;
v_isShared_1697_ = v_isSharedCheck_1704_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_val_1694_);
lean_dec(v_x_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1704_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1699_ = lean_expr_dbg_to_string(v_val_1694_);
lean_dec(v_val_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 3);
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1698_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_1711_, lean_object* v_lctx_1712_, lean_object* v_stx_1713_, lean_object* v_expectedType_x3f_1714_, lean_object* v_info_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1740_; 
v___x_1721_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1711_, v_lctx_1712_, v_stx_1713_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1740_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1740_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_1727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
v___x_1728_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1714_);
v___x_1731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_Elab_CompletionInfo_stx(v_info_1715_);
v___x_1735_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1711_, v___x_1734_);
lean_dec(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1733_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1736_);
v___x_1738_ = v___x_1724_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_1741_, lean_object* v_lctx_1742_, lean_object* v_stx_1743_, lean_object* v_expectedType_x3f_1744_, lean_object* v_info_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_1741_, v_lctx_1742_, v_stx_1743_, v_expectedType_x3f_1744_, v_info_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_info_1745_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_1758_, lean_object* v_info_1759_){
_start:
{
switch(lean_obj_tag(v_info_1759_))
{
case 0:
{
lean_object* v_termInfo_1761_; lean_object* v_expectedType_x3f_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1783_; 
v_termInfo_1761_ = lean_ctor_get(v_info_1759_, 0);
v_expectedType_x3f_1762_ = lean_ctor_get(v_info_1759_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_info_1759_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1764_ = v_info_1759_;
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_expectedType_x3f_1762_);
lean_inc(v_termInfo_1761_);
lean_dec(v_info_1759_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Elab_TermInfo_format(v_ctx_1758_, v_termInfo_1761_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1782_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1782_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1782_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 5);
lean_ctor_set(v___x_1764_, 1, v_a_1767_);
lean_ctor_set(v___x_1764_, 0, v___x_1771_);
v___x_1773_ = v___x_1764_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_a_1767_);
v___x_1773_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1774_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_1762_);
v___x_1777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1777_);
v___x_1779_ = v___x_1769_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_del_object(v___x_1764_);
lean_dec(v_expectedType_x3f_1762_);
return v___x_1766_;
}
}
}
case 1:
{
lean_object* v_stx_1784_; lean_object* v_lctx_1785_; lean_object* v_expectedType_x3f_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; 
v_stx_1784_ = lean_ctor_get(v_info_1759_, 0);
lean_inc(v_stx_1784_);
v_lctx_1785_ = lean_ctor_get(v_info_1759_, 2);
lean_inc_ref(v_lctx_1785_);
v_expectedType_x3f_1786_ = lean_ctor_get(v_info_1759_, 3);
lean_inc(v_expectedType_x3f_1786_);
lean_inc_ref(v_lctx_1785_);
lean_inc_ref(v_ctx_1758_);
v___f_1787_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1787_, 0, v_ctx_1758_);
lean_closure_set(v___f_1787_, 1, v_lctx_1785_);
lean_closure_set(v___f_1787_, 2, v_stx_1784_);
lean_closure_set(v___f_1787_, 3, v_expectedType_x3f_1786_);
lean_closure_set(v___f_1787_, 4, v_info_1759_);
v___x_1788_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1758_, v_lctx_1785_, v___f_1787_);
return v___x_1788_;
}
default: 
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1789_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_1790_ = l_Lean_Elab_CompletionInfo_stx(v_info_1759_);
lean_dec_ref(v_info_1759_);
v___x_1791_ = lean_box(0);
v___x_1792_ = 0;
lean_inc(v___x_1790_);
v___x_1793_ = l_Lean_Syntax_formatStx(v___x_1790_, v___x_1791_, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1789_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1758_, v___x_1790_);
lean_dec(v___x_1790_);
v___x_1798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_1800_, lean_object* v_info_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1800_, v_info_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_1807_, lean_object* v_info_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_1811_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1807_, v_info_1808_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_1814_, lean_object* v_info_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Elab_CommandInfo_format(v_ctx_1814_, v_info_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_1821_, lean_object* v_info_1822_){
_start:
{
lean_object* v_stx_1824_; lean_object* v_optionName_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_stx_1824_ = lean_ctor_get(v_info_1822_, 0);
lean_inc(v_stx_1824_);
v_optionName_1825_ = lean_ctor_get(v_info_1822_, 1);
lean_inc(v_optionName_1825_);
lean_dec_ref(v_info_1822_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Name_toString(v_optionName_1825_, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1826_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1821_, v_stx_1824_);
lean_dec(v_stx_1824_);
v___x_1834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_1836_, lean_object* v_info_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_OptionInfo_format(v_ctx_1836_, v_info_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_1843_, lean_object* v_info_1844_){
_start:
{
lean_object* v_stx_1846_; lean_object* v_errorName_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1863_; 
v_stx_1846_ = lean_ctor_get(v_info_1844_, 0);
v_errorName_1847_ = lean_ctor_get(v_info_1844_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_info_1844_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1849_ = v_info_1844_;
v_isShared_1850_ = v_isSharedCheck_1863_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_errorName_1847_);
lean_inc(v_stx_1846_);
lean_dec(v_info_1844_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1863_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1851_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_1852_ = 1;
v___x_1853_ = l_Lean_Name_toString(v_errorName_1847_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 5);
lean_ctor_set(v___x_1849_, 1, v___x_1854_);
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1843_, v_stx_1846_);
lean_dec(v_stx_1846_);
v___x_1860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_1864_, lean_object* v_info_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1864_, v_info_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1874_, lean_object* v_fieldName_1875_, lean_object* v_ctx_1876_, lean_object* v_stx_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc_ref(v_val_1874_);
v___x_1883_ = lean_infer_type(v_val_1874_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Meta_ppExpr(v_a_1884_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1916_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_Meta_ppExpr(v_val_1874_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1895_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1896_ = 1;
v___x_1897_ = l_Lean_Name_toString(v_fieldName_1875_, v___x_1896_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 3);
lean_ctor_set(v___x_1888_, 0, v___x_1897_);
v___x_1899_ = v___x_1888_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1895_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1886_);
v___x_1904_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_a_1891_);
v___x_1907_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1876_, v_stx_1877_);
v___x_1910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1910_);
v___x_1912_ = v___x_1893_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_del_object(v___x_1888_);
lean_dec(v_a_1886_);
lean_dec_ref(v_ctx_1876_);
lean_dec(v_fieldName_1875_);
return v___x_1890_;
}
}
}
else
{
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_ctx_1876_);
lean_dec(v_fieldName_1875_);
lean_dec_ref(v_val_1874_);
return v___x_1885_;
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_ctx_1876_);
lean_dec(v_fieldName_1875_);
lean_dec_ref(v_val_1874_);
v_a_1917_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1883_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1883_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1925_, lean_object* v_fieldName_1926_, lean_object* v_ctx_1927_, lean_object* v_stx_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1925_, v_fieldName_1926_, v_ctx_1927_, v_stx_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v_stx_1928_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1935_, lean_object* v_info_1936_){
_start:
{
lean_object* v_fieldName_1938_; lean_object* v_lctx_1939_; lean_object* v_val_1940_; lean_object* v_stx_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v_fieldName_1938_ = lean_ctor_get(v_info_1936_, 1);
lean_inc(v_fieldName_1938_);
v_lctx_1939_ = lean_ctor_get(v_info_1936_, 2);
lean_inc_ref(v_lctx_1939_);
v_val_1940_ = lean_ctor_get(v_info_1936_, 3);
lean_inc_ref(v_val_1940_);
v_stx_1941_ = lean_ctor_get(v_info_1936_, 4);
lean_inc(v_stx_1941_);
lean_dec_ref(v_info_1936_);
lean_inc_ref(v_ctx_1935_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1942_, 0, v_val_1940_);
lean_closure_set(v___f_1942_, 1, v_fieldName_1938_);
lean_closure_set(v___f_1942_, 2, v_ctx_1935_);
lean_closure_set(v___f_1942_, 3, v_stx_1941_);
v___x_1943_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1935_, v_lctx_1939_, v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1944_, lean_object* v_info_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_FieldInfo_format(v_ctx_1944_, v_info_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
lean_dec(v_pre_1948_);
return v_x_1949_;
}
else
{
lean_object* v_head_1951_; lean_object* v_tail_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1961_; 
v_head_1951_ = lean_ctor_get(v_x_1950_, 0);
v_tail_1952_ = lean_ctor_get(v_x_1950_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1954_ = v_x_1950_;
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_tail_1952_);
lean_inc(v_head_1951_);
lean_dec(v_x_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
lean_inc(v_pre_1948_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 5);
lean_ctor_set(v___x_1954_, 1, v_pre_1948_);
lean_ctor_set(v___x_1954_, 0, v_x_1949_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_x_1949_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_pre_1948_);
v___x_1957_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v_head_1951_);
v_x_1949_ = v___x_1958_;
v_x_1950_ = v_tail_1952_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1962_, lean_object* v_x_1963_){
_start:
{
if (lean_obj_tag(v_x_1963_) == 0)
{
lean_object* v___x_1964_; 
lean_dec(v_pre_1962_);
v___x_1964_ = lean_box(0);
return v___x_1964_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_head_1965_ = lean_ctor_get(v_x_1963_, 0);
v_tail_1966_ = lean_ctor_get(v_x_1963_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v_x_1963_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_tail_1966_);
lean_inc(v_head_1965_);
lean_dec(v_x_1963_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
lean_inc(v_pre_1962_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 5);
lean_ctor_set(v___x_1968_, 1, v_head_1965_);
lean_ctor_set(v___x_1968_, 0, v_pre_1962_);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_pre_1962_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_head_1965_);
v___x_1971_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1962_, v___x_1971_, v_tail_1966_);
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
v___x_1982_ = l_List_reverse___redArg(v_x_1976_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
else
{
lean_object* v_head_1984_; lean_object* v_tail_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2003_; 
v_head_1984_ = lean_ctor_get(v_x_1975_, 0);
v_tail_1985_ = lean_ctor_get(v_x_1975_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1975_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1987_ = v_x_1975_;
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_tail_1985_);
lean_inc(v_head_1984_);
lean_dec(v_x_1975_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; 
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
lean_inc(v___y_1978_);
lean_inc_ref(v___y_1977_);
v___x_1989_ = l_Lean_Meta_ppGoal(v_head_1984_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v_head_1984_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_x_1976_);
lean_ctor_set(v___x_1987_, 0, v_a_1990_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_x_1976_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_x_1975_ = v_tail_1985_;
v_x_1976_ = v___x_1992_;
goto _start;
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_del_object(v___x_1987_);
lean_dec(v_tail_1985_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_x_1976_);
v_a_1995_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1989_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_2015_, lean_object* v___x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_2015_, v___x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2032_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2032_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2032_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2027_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2028_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2027_, v_a_2023_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2028_);
v___x_2030_ = v___x_2025_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_a_2033_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2022_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2022_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_2041_, lean_object* v___x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_2041_, v___x_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v_res_2048_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_unsigned_to_nat(32u);
v___x_2053_ = lean_mk_empty_array_with_capacity(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2055_ = ((size_t)5ULL);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = lean_unsigned_to_nat(32u);
v___x_2058_ = lean_mk_empty_array_with_capacity(v___x_2057_);
v___x_2059_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2060_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___x_2058_);
lean_ctor_set(v___x_2060_, 2, v___x_2056_);
lean_ctor_set(v___x_2060_, 3, v___x_2056_);
lean_ctor_set_usize(v___x_2060_, 4, v___x_2055_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_box(1);
v___x_2062_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2063_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_2064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
lean_ctor_set(v___x_2064_, 2, v___x_2061_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_2068_, lean_object* v_goals_2069_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = l_List_isEmpty___redArg(v_goals_2069_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; 
v___x_2072_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_2073_ = lean_box(0);
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2074_, 0, v_goals_2069_);
lean_closure_set(v___f_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_2068_, v___x_2072_, v___f_2074_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_goals_2069_);
lean_dec_ref(v_ctx_2068_);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_2078_, lean_object* v_goals_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_2078_, v_goals_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_2091_, lean_object* v_info_2092_){
_start:
{
lean_object* v_toCommandContextInfo_2094_; lean_object* v_parentDecl_x3f_2095_; lean_object* v_autoImplicits_2096_; lean_object* v_env_2097_; lean_object* v_cmdEnv_x3f_2098_; lean_object* v_fileMap_2099_; lean_object* v_options_2100_; lean_object* v_currNamespace_2101_; lean_object* v_openDecls_2102_; lean_object* v_ngen_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2145_; 
v_toCommandContextInfo_2094_ = lean_ctor_get(v_ctx_2091_, 0);
lean_inc_ref(v_toCommandContextInfo_2094_);
v_parentDecl_x3f_2095_ = lean_ctor_get(v_ctx_2091_, 1);
v_autoImplicits_2096_ = lean_ctor_get(v_ctx_2091_, 2);
v_env_2097_ = lean_ctor_get(v_toCommandContextInfo_2094_, 0);
v_cmdEnv_x3f_2098_ = lean_ctor_get(v_toCommandContextInfo_2094_, 1);
v_fileMap_2099_ = lean_ctor_get(v_toCommandContextInfo_2094_, 2);
v_options_2100_ = lean_ctor_get(v_toCommandContextInfo_2094_, 4);
v_currNamespace_2101_ = lean_ctor_get(v_toCommandContextInfo_2094_, 5);
v_openDecls_2102_ = lean_ctor_get(v_toCommandContextInfo_2094_, 6);
v_ngen_2103_ = lean_ctor_get(v_toCommandContextInfo_2094_, 7);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_toCommandContextInfo_2094_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_toCommandContextInfo_2094_, 3);
lean_dec(v_unused_2146_);
v___x_2105_ = v_toCommandContextInfo_2094_;
v_isShared_2106_ = v_isSharedCheck_2145_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_ngen_2103_);
lean_inc(v_openDecls_2102_);
lean_inc(v_currNamespace_2101_);
lean_inc(v_options_2100_);
lean_inc(v_fileMap_2099_);
lean_inc(v_cmdEnv_x3f_2098_);
lean_inc(v_env_2097_);
lean_dec(v_toCommandContextInfo_2094_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2145_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_toElabInfo_2107_; lean_object* v_mctxBefore_2108_; lean_object* v_goalsBefore_2109_; lean_object* v_mctxAfter_2110_; lean_object* v_goalsAfter_2111_; lean_object* v___x_2113_; 
v_toElabInfo_2107_ = lean_ctor_get(v_info_2092_, 0);
lean_inc_ref(v_toElabInfo_2107_);
v_mctxBefore_2108_ = lean_ctor_get(v_info_2092_, 1);
lean_inc_ref(v_mctxBefore_2108_);
v_goalsBefore_2109_ = lean_ctor_get(v_info_2092_, 2);
lean_inc(v_goalsBefore_2109_);
v_mctxAfter_2110_ = lean_ctor_get(v_info_2092_, 3);
lean_inc_ref(v_mctxAfter_2110_);
v_goalsAfter_2111_ = lean_ctor_get(v_info_2092_, 4);
lean_inc(v_goalsAfter_2111_);
lean_dec_ref(v_info_2092_);
lean_inc_ref(v_ngen_2103_);
lean_inc(v_openDecls_2102_);
lean_inc(v_currNamespace_2101_);
lean_inc_ref(v_options_2100_);
lean_inc_ref(v_fileMap_2099_);
lean_inc(v_cmdEnv_x3f_2098_);
lean_inc_ref(v_env_2097_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 3, v_mctxBefore_2108_);
v___x_2113_ = v___x_2105_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_env_2097_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_cmdEnv_x3f_2098_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_fileMap_2099_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_mctxBefore_2108_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_options_2100_);
lean_ctor_set(v_reuseFailAlloc_2144_, 5, v_currNamespace_2101_);
lean_ctor_set(v_reuseFailAlloc_2144_, 6, v_openDecls_2102_);
lean_ctor_set(v_reuseFailAlloc_2144_, 7, v_ngen_2103_);
v___x_2113_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v_ctxB_2114_; lean_object* v___x_2115_; 
lean_inc_ref(v_autoImplicits_2096_);
lean_inc(v_parentDecl_x3f_2095_);
v_ctxB_2114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_2114_, 0, v___x_2113_);
lean_ctor_set(v_ctxB_2114_, 1, v_parentDecl_x3f_2095_);
lean_ctor_set(v_ctxB_2114_, 2, v_autoImplicits_2096_);
v___x_2115_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_2114_, v_goalsBefore_2109_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; lean_object* v_ctxA_2118_; lean_object* v___x_2119_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2117_, 0, v_env_2097_);
lean_ctor_set(v___x_2117_, 1, v_cmdEnv_x3f_2098_);
lean_ctor_set(v___x_2117_, 2, v_fileMap_2099_);
lean_ctor_set(v___x_2117_, 3, v_mctxAfter_2110_);
lean_ctor_set(v___x_2117_, 4, v_options_2100_);
lean_ctor_set(v___x_2117_, 5, v_currNamespace_2101_);
lean_ctor_set(v___x_2117_, 6, v_openDecls_2102_);
lean_ctor_set(v___x_2117_, 7, v_ngen_2103_);
lean_inc_ref(v_autoImplicits_2096_);
lean_inc(v_parentDecl_x3f_2095_);
v_ctxA_2118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_2118_, 0, v___x_2117_);
lean_ctor_set(v_ctxA_2118_, 1, v_parentDecl_x3f_2095_);
lean_ctor_set(v_ctxA_2118_, 2, v_autoImplicits_2096_);
v___x_2119_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_2118_, v_goalsAfter_2111_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2143_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2143_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2143_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_stx_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v_stx_2124_ = lean_ctor_get(v_toElabInfo_2107_, 1);
lean_inc(v_stx_2124_);
v___x_2125_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_2126_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2091_, v_toElabInfo_2107_);
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_box(0);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Syntax_formatStx(v_stx_2124_, v___x_2130_, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2129_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_2135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v_a_2116_);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_a_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2139_);
v___x_2141_ = v___x_2122_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
else
{
lean_dec(v_a_2116_);
lean_dec_ref(v_toElabInfo_2107_);
lean_dec_ref(v_ctx_2091_);
return v___x_2119_;
}
}
else
{
lean_dec(v_goalsAfter_2111_);
lean_dec_ref(v_mctxAfter_2110_);
lean_dec_ref(v_toElabInfo_2107_);
lean_dec_ref(v_ngen_2103_);
lean_dec(v_openDecls_2102_);
lean_dec(v_currNamespace_2101_);
lean_dec_ref(v_options_2100_);
lean_dec_ref(v_fileMap_2099_);
lean_dec(v_cmdEnv_x3f_2098_);
lean_dec_ref(v_env_2097_);
lean_dec_ref(v_ctx_2091_);
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_2147_, lean_object* v_info_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Elab_TacticInfo_format(v_ctx_2147_, v_info_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_2157_, lean_object* v_info_2158_){
_start:
{
lean_object* v_lctx_2160_; lean_object* v_stx_2161_; lean_object* v_output_2162_; lean_object* v___x_2163_; lean_object* v_a_2164_; lean_object* v___x_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2178_; 
v_lctx_2160_ = lean_ctor_get(v_info_2158_, 0);
lean_inc_ref(v_lctx_2160_);
v_stx_2161_ = lean_ctor_get(v_info_2158_, 1);
lean_inc(v_stx_2161_);
v_output_2162_ = lean_ctor_get(v_info_2158_, 2);
lean_inc(v_output_2162_);
lean_dec_ref(v_info_2158_);
lean_inc_ref(v_lctx_2160_);
v___x_2163_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2157_, v_lctx_2160_, v_stx_2161_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_2157_, v_lctx_2160_, v_output_2162_);
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2170_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v_a_2164_);
v___x_2172_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_a_2166_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2174_);
v___x_2176_ = v___x_2168_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_2179_, lean_object* v_info_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2179_, v_info_2180_);
lean_dec_ref(v_ctx_2179_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
size_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_2188_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_ctor_set_usize(v___x_2188_, 2, v___x_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_2192_){
_start:
{
lean_object* v_toWidgetInstance_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2222_; 
v_toWidgetInstance_2193_ = lean_ctor_get(v_info_2192_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_info_2192_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_info_2192_, 1);
lean_dec(v_unused_2223_);
v___x_2195_ = v_info_2192_;
v_isShared_2196_ = v_isSharedCheck_2222_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_toWidgetInstance_2193_);
lean_dec(v_info_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2222_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_id_2197_; lean_object* v_props_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v_fst_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2220_; 
v_id_2197_ = lean_ctor_get(v_toWidgetInstance_2193_, 0);
lean_inc(v_id_2197_);
v_props_2198_ = lean_ctor_get(v_toWidgetInstance_2193_, 1);
lean_inc_ref(v_props_2198_);
lean_dec_ref(v_toWidgetInstance_2193_);
v___x_2199_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_2200_ = lean_apply_1(v_props_2198_, v___x_2199_);
v_fst_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2200_, 1);
lean_dec(v_unused_2221_);
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2220_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_fst_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2220_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2205_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_2206_ = 1;
v___x_2207_ = l_Lean_Name_toString(v_id_2197_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 5);
lean_ctor_set(v___x_2203_, 1, v___x_2208_);
lean_ctor_set(v___x_2203_, 0, v___x_2205_);
v___x_2210_ = v___x_2203_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 5);
lean_ctor_set(v___x_2195_, 1, v___x_2211_);
lean_ctor_set(v___x_2195_, 0, v___x_2210_);
v___x_2213_ = v___x_2195_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_unsigned_to_nat(80u);
v___x_2215_ = l_Lean_Json_pretty(v_fst_2201_, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2213_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
return v___x_2217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_2230_){
_start:
{
lean_object* v_userName_2231_; lean_object* v_id_2232_; lean_object* v_baseId_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_userName_2231_ = lean_ctor_get(v_info_2230_, 0);
lean_inc(v_userName_2231_);
v_id_2232_ = lean_ctor_get(v_info_2230_, 1);
lean_inc(v_id_2232_);
v_baseId_2233_ = lean_ctor_get(v_info_2230_, 2);
lean_inc(v_baseId_2233_);
lean_dec_ref(v_info_2230_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_2235_ = lean_erase_macro_scopes(v_userName_2231_);
v___x_2236_ = 1;
v___x_2237_ = l_Lean_Name_toString(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2234_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_Name_toString(v_id_2232_, v___x_2236_);
v___x_2243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2241_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = l_Lean_Name_toString(v_baseId_2233_, v___x_2236_);
v___x_2248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2246_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_2253_, lean_object* v_info_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_2256_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_2253_, v_info_2254_);
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_2258_, lean_object* v_info_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2258_, v_info_2259_);
lean_dec(v_info_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2275_; 
v_val_2264_ = lean_ctor_get(v_x_2261_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2266_ = v_x_2261_;
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v_x_2261_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_2269_ = l_String_quote(v_val_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 3);
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2268_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Repr_addAppParen(v___x_2272_, v_x_2262_);
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_2276_, v_x_2277_);
lean_dec(v_x_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_2293_, lean_object* v_info_2294_){
_start:
{
lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v_toTermInfo_2302_; lean_object* v_location_x3f_2303_; lean_object* v_docString_x3f_2304_; uint8_t v_explicit_2305_; lean_object* v___y_2307_; 
v_toTermInfo_2302_ = lean_ctor_get(v_info_2294_, 0);
lean_inc_ref(v_toTermInfo_2302_);
v_location_x3f_2303_ = lean_ctor_get(v_info_2294_, 1);
lean_inc(v_location_x3f_2303_);
v_docString_x3f_2304_ = lean_ctor_get(v_info_2294_, 2);
lean_inc(v_docString_x3f_2304_);
v_explicit_2305_ = lean_ctor_get_uint8(v_info_2294_, sizeof(void*)*3);
lean_dec_ref(v_info_2294_);
if (lean_obj_tag(v_location_x3f_2303_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2385_; 
v_val_2324_ = lean_ctor_get(v_location_x3f_2303_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_location_x3f_2303_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2326_ = v_location_x3f_2303_;
v_isShared_2327_ = v_isSharedCheck_2385_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_location_x3f_2303_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2385_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_range_2328_; lean_object* v_pos_2329_; lean_object* v_endPos_2330_; lean_object* v_module_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2383_; 
v_range_2328_ = lean_ctor_get(v_val_2324_, 1);
v_pos_2329_ = lean_ctor_get(v_range_2328_, 0);
lean_inc_ref(v_pos_2329_);
v_endPos_2330_ = lean_ctor_get(v_range_2328_, 2);
lean_inc_ref(v_endPos_2330_);
v_module_2331_ = lean_ctor_get(v_val_2324_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_val_2324_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v_val_2324_, 1);
lean_dec(v_unused_2384_);
v___x_2333_ = v_val_2324_;
v_isShared_2334_ = v_isSharedCheck_2383_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_module_2331_);
lean_dec(v_val_2324_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2383_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_line_2335_; lean_object* v_column_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2382_; 
v_line_2335_ = lean_ctor_get(v_pos_2329_, 0);
v_column_2336_ = lean_ctor_get(v_pos_2329_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_pos_2329_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2338_ = v_pos_2329_;
v_isShared_2339_ = v_isSharedCheck_2382_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_column_2336_);
lean_inc(v_line_2335_);
lean_dec(v_pos_2329_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2382_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_line_2340_; lean_object* v_column_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2381_; 
v_line_2340_ = lean_ctor_get(v_endPos_2330_, 0);
v_column_2341_ = lean_ctor_get(v_endPos_2330_, 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_endPos_2330_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2343_ = v_endPos_2330_;
v_isShared_2344_ = v_isSharedCheck_2381_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_column_2341_);
lean_inc(v_line_2340_);
lean_dec(v_endPos_2330_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2381_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = 1;
v___x_2346_ = l_Lean_Name_toString(v_module_2331_, v___x_2345_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 3);
lean_ctor_set(v___x_2326_, 0, v___x_2346_);
v___x_2348_ = v___x_2326_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 5);
lean_ctor_set(v___x_2343_, 1, v___x_2349_);
lean_ctor_set(v___x_2343_, 0, v___x_2348_);
v___x_2351_ = v___x_2343_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2352_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_2353_ = l_Nat_reprFast(v_line_2335_);
v___x_2354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 5);
lean_ctor_set(v___x_2338_, 1, v___x_2354_);
lean_ctor_set(v___x_2338_, 0, v___x_2352_);
v___x_2356_ = v___x_2338_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 5);
lean_ctor_set(v___x_2333_, 1, v___x_2357_);
lean_ctor_set(v___x_2333_, 0, v___x_2356_);
v___x_2359_ = v___x_2333_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2360_ = l_Nat_reprFast(v_column_2336_);
v___x_2361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2359_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_2364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2351_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_2367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Nat_reprFast(v_line_2340_);
v___x_2369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2352_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2357_);
v___x_2372_ = l_Nat_reprFast(v_column_2341_);
v___x_2373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2363_);
v___x_2376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2367_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___y_2307_ = v___x_2376_;
goto v___jp_2306_;
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
lean_object* v___x_2386_; 
lean_dec(v_location_x3f_2303_);
v___x_2386_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_2307_ = v___x_2386_;
goto v___jp_2306_;
}
v___jp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2298_);
v___x_2300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___y_2297_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
v___jp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Elab_TermInfo_format(v_ctx_2293_, v_toTermInfo_2302_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_2311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_a_2309_);
v___x_2312_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_2313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___y_2307_);
v___x_2315_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_2316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_docString_x3f_2304_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2316_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_2321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
if (v_explicit_2305_ == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_2297_ = v___x_2321_;
v___y_2298_ = v___x_2322_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_2297_ = v___x_2321_;
v___y_2298_ = v___x_2323_;
goto v___jp_2296_;
}
}
else
{
lean_dec(v___y_2307_);
lean_dec(v_docString_x3f_2304_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_2387_, lean_object* v_info_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2387_, v_info_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_2394_, lean_object* v_info_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_2397_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2394_, v_info_2395_);
v___x_2398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_2402_, lean_object* v_info_2403_){
_start:
{
lean_object* v_stx_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_stx_2404_ = lean_ctor_get(v_info_2403_, 1);
v___x_2405_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_2404_);
v___x_2406_ = l_Lean_Syntax_getKind(v_stx_2404_);
v___x_2407_ = 1;
v___x_2408_ = l_Lean_Name_toString(v___x_2406_, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2405_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_2412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2402_, v_info_2403_);
v___x_2414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_2424_, lean_object* v_info_2425_){
_start:
{
lean_object* v_toElabInfo_2426_; lean_object* v_name_2427_; uint8_t v_kind_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_toElabInfo_2426_ = lean_ctor_get(v_info_2425_, 0);
lean_inc_ref(v_toElabInfo_2426_);
v_name_2427_ = lean_ctor_get(v_info_2425_, 1);
lean_inc(v_name_2427_);
v_kind_2428_ = lean_ctor_get_uint8(v_info_2425_, sizeof(void*)*2);
lean_dec_ref(v_info_2425_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_2430_ = 1;
v___x_2431_ = l_Lean_Name_toString(v_name_2427_, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2429_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_2435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_2428_, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2435_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_2424_, v_toElabInfo_2426_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_2443_, lean_object* v_x_2444_){
_start:
{
switch(lean_obj_tag(v_x_2444_))
{
case 0:
{
lean_object* v_i_2446_; lean_object* v___x_2447_; 
v_i_2446_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2446_);
lean_dec_ref(v_x_2444_);
v___x_2447_ = l_Lean_Elab_TacticInfo_format(v_ctx_2443_, v_i_2446_);
return v___x_2447_;
}
case 1:
{
lean_object* v_i_2448_; lean_object* v___x_2449_; 
v_i_2448_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2448_);
lean_dec_ref(v_x_2444_);
v___x_2449_ = l_Lean_Elab_TermInfo_format(v_ctx_2443_, v_i_2448_);
return v___x_2449_;
}
case 2:
{
lean_object* v_i_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2458_; 
v_i_2450_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2452_ = v_x_2444_;
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_i_2450_);
lean_dec(v_x_2444_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_2443_, v_i_2450_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
case 3:
{
lean_object* v_i_2459_; lean_object* v___x_2460_; 
v_i_2459_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2459_);
lean_dec_ref(v_x_2444_);
v___x_2460_ = l_Lean_Elab_CommandInfo_format(v_ctx_2443_, v_i_2459_);
return v___x_2460_;
}
case 4:
{
lean_object* v_i_2461_; lean_object* v___x_2462_; 
v_i_2461_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2461_);
lean_dec_ref(v_x_2444_);
v___x_2462_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_2443_, v_i_2461_);
lean_dec_ref(v_ctx_2443_);
return v___x_2462_;
}
case 5:
{
lean_object* v_i_2463_; lean_object* v___x_2464_; 
v_i_2463_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2463_);
lean_dec_ref(v_x_2444_);
v___x_2464_ = l_Lean_Elab_OptionInfo_format(v_ctx_2443_, v_i_2463_);
return v___x_2464_;
}
case 6:
{
lean_object* v_i_2465_; lean_object* v___x_2466_; 
v_i_2465_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2465_);
lean_dec_ref(v_x_2444_);
v___x_2466_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_2443_, v_i_2465_);
return v___x_2466_;
}
case 7:
{
lean_object* v_i_2467_; lean_object* v___x_2468_; 
v_i_2467_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2467_);
lean_dec_ref(v_x_2444_);
v___x_2468_ = l_Lean_Elab_FieldInfo_format(v_ctx_2443_, v_i_2467_);
return v___x_2468_;
}
case 8:
{
lean_object* v_i_2469_; lean_object* v___x_2470_; 
v_i_2469_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2469_);
lean_dec_ref(v_x_2444_);
v___x_2470_ = l_Lean_Elab_CompletionInfo_format(v_ctx_2443_, v_i_2469_);
return v___x_2470_;
}
case 9:
{
lean_object* v_i_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_ctx_2443_);
v_i_2471_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2473_ = v_x_2444_;
v_isShared_2474_ = v_isSharedCheck_2479_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_i_2471_);
lean_dec(v_x_2444_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2479_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = l_Lean_Elab_UserWidgetInfo_format(v_i_2471_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
case 10:
{
lean_object* v_i_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_ctx_2443_);
v_i_2480_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2482_ = v_x_2444_;
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_i_2480_);
lean_dec(v_x_2444_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = l_Lean_Elab_CustomInfo_format(v_i_2480_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2484_);
v___x_2486_ = v___x_2482_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
case 11:
{
lean_object* v_i_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
lean_dec_ref(v_ctx_2443_);
v_i_2489_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v_x_2444_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_i_2489_);
lean_dec(v_x_2444_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = l_Lean_Elab_FVarAliasInfo_format(v_i_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
case 12:
{
lean_object* v_i_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2506_; 
v_i_2498_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2500_ = v_x_2444_;
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_i_2498_);
lean_dec(v_x_2444_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_2443_, v_i_2498_);
lean_dec(v_i_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
case 13:
{
lean_object* v_i_2507_; lean_object* v___x_2508_; 
v_i_2507_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_ref(v_i_2507_);
lean_dec_ref(v_x_2444_);
v___x_2508_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_2443_, v_i_2507_);
return v___x_2508_;
}
case 14:
{
lean_object* v_i_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2517_; 
v_i_2509_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2511_ = v_x_2444_;
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_i_2509_);
lean_dec(v_x_2444_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_2443_, v_i_2509_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
case 15:
{
lean_object* v_i_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
v_i_2518_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v_x_2444_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_i_2518_);
lean_dec(v_x_2444_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = l_Lean_Elab_DocInfo_format(v_ctx_2443_, v_i_2518_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
default: 
{
lean_object* v_i_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2535_; 
v_i_2527_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2529_ = v_x_2444_;
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_i_2527_);
lean_dec(v_x_2444_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = l_Lean_Elab_DocElabInfo_format(v_ctx_2443_, v_i_2527_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_2536_, lean_object* v_x_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_Elab_Info_format(v_ctx_2536_, v_x_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object* v_x_2540_){
_start:
{
switch(lean_obj_tag(v_x_2540_))
{
case 0:
{
lean_object* v_i_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
v_i_2541_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2543_ = v_x_2540_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_i_2541_);
lean_dec(v_x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_toElabInfo_2545_; lean_object* v___x_2547_; 
v_toElabInfo_2545_ = lean_ctor_get(v_i_2541_, 0);
lean_inc_ref(v_toElabInfo_2545_);
lean_dec_ref(v_i_2541_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
lean_ctor_set(v___x_2543_, 0, v_toElabInfo_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_toElabInfo_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
case 1:
{
lean_object* v_i_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
v_i_2550_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v_x_2540_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_i_2550_);
lean_dec(v_x_2540_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_toElabInfo_2554_; lean_object* v___x_2556_; 
v_toElabInfo_2554_ = lean_ctor_get(v_i_2550_, 0);
lean_inc_ref(v_toElabInfo_2554_);
lean_dec_ref(v_i_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v_toElabInfo_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_toElabInfo_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
case 2:
{
lean_object* v_i_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2567_; 
v_i_2559_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2561_ = v_x_2540_;
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_i_2559_);
lean_dec(v_x_2540_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_toElabInfo_2563_; lean_object* v___x_2565_; 
v_toElabInfo_2563_ = lean_ctor_get(v_i_2559_, 0);
lean_inc_ref(v_toElabInfo_2563_);
lean_dec_ref(v_i_2559_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 1);
lean_ctor_set(v___x_2561_, 0, v_toElabInfo_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_toElabInfo_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
case 3:
{
lean_object* v_i_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_i_2568_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v_x_2540_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_i_2568_);
lean_dec(v_x_2540_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 1);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_i_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
case 13:
{
lean_object* v_i_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2585_; 
v_i_2576_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2578_ = v_x_2540_;
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_i_2576_);
lean_dec(v_x_2540_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_toTermInfo_2580_; lean_object* v_toElabInfo_2581_; lean_object* v___x_2583_; 
v_toTermInfo_2580_ = lean_ctor_get(v_i_2576_, 0);
lean_inc_ref(v_toTermInfo_2580_);
lean_dec_ref(v_i_2576_);
v_toElabInfo_2581_ = lean_ctor_get(v_toTermInfo_2580_, 0);
lean_inc_ref(v_toElabInfo_2581_);
lean_dec_ref(v_toTermInfo_2580_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 0, v_toElabInfo_2581_);
v___x_2583_ = v___x_2578_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_toElabInfo_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
case 14:
{
lean_object* v_i_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_i_2586_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v_x_2540_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_i_2586_);
lean_dec(v_x_2540_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 1);
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_i_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
case 15:
{
lean_object* v_i_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_i_2594_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v_x_2540_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_i_2594_);
lean_dec(v_x_2540_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 1);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_i_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
case 16:
{
lean_object* v_i_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
v_i_2602_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2604_ = v_x_2540_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_i_2602_);
lean_dec(v_x_2540_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_toElabInfo_2606_; lean_object* v___x_2608_; 
v_toElabInfo_2606_ = lean_ctor_get(v_i_2602_, 0);
lean_inc_ref(v_toElabInfo_2606_);
lean_dec_ref(v_i_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 1);
lean_ctor_set(v___x_2604_, 0, v_toElabInfo_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_toElabInfo_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
default: 
{
lean_object* v___x_2611_; 
lean_dec_ref(v_x_2540_);
v___x_2611_ = lean_box(0);
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
if (lean_obj_tag(v_x_2612_) == 1)
{
if (lean_obj_tag(v_x_2613_) == 0)
{
lean_object* v_val_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2649_; 
v_val_2614_ = lean_ctor_get(v_x_2612_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_x_2612_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2616_ = v_x_2612_;
v_isShared_2617_ = v_isSharedCheck_2649_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_val_2614_);
lean_dec(v_x_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2649_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_toCommandContextInfo_2618_; lean_object* v_i_2619_; lean_object* v_parentDecl_x3f_2620_; lean_object* v_autoImplicits_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2647_; 
v_toCommandContextInfo_2618_ = lean_ctor_get(v_val_2614_, 0);
lean_inc_ref(v_toCommandContextInfo_2618_);
v_i_2619_ = lean_ctor_get(v_x_2613_, 0);
v_parentDecl_x3f_2620_ = lean_ctor_get(v_val_2614_, 1);
v_autoImplicits_2621_ = lean_ctor_get(v_val_2614_, 2);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_val_2614_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_val_2614_, 0);
lean_dec(v_unused_2648_);
v___x_2623_ = v_val_2614_;
v_isShared_2624_ = v_isSharedCheck_2647_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_autoImplicits_2621_);
lean_inc(v_parentDecl_x3f_2620_);
lean_dec(v_val_2614_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2647_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_env_2625_; lean_object* v_cmdEnv_x3f_2626_; lean_object* v_fileMap_2627_; lean_object* v_options_2628_; lean_object* v_currNamespace_2629_; lean_object* v_openDecls_2630_; lean_object* v_ngen_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2645_; 
v_env_2625_ = lean_ctor_get(v_toCommandContextInfo_2618_, 0);
v_cmdEnv_x3f_2626_ = lean_ctor_get(v_toCommandContextInfo_2618_, 1);
v_fileMap_2627_ = lean_ctor_get(v_toCommandContextInfo_2618_, 2);
v_options_2628_ = lean_ctor_get(v_toCommandContextInfo_2618_, 4);
v_currNamespace_2629_ = lean_ctor_get(v_toCommandContextInfo_2618_, 5);
v_openDecls_2630_ = lean_ctor_get(v_toCommandContextInfo_2618_, 6);
v_ngen_2631_ = lean_ctor_get(v_toCommandContextInfo_2618_, 7);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_toCommandContextInfo_2618_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v_toCommandContextInfo_2618_, 3);
lean_dec(v_unused_2646_);
v___x_2633_ = v_toCommandContextInfo_2618_;
v_isShared_2634_ = v_isSharedCheck_2645_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_ngen_2631_);
lean_inc(v_openDecls_2630_);
lean_inc(v_currNamespace_2629_);
lean_inc(v_options_2628_);
lean_inc(v_fileMap_2627_);
lean_inc(v_cmdEnv_x3f_2626_);
lean_inc(v_env_2625_);
lean_dec(v_toCommandContextInfo_2618_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2645_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_mctxAfter_2635_; lean_object* v___x_2637_; 
v_mctxAfter_2635_ = lean_ctor_get(v_i_2619_, 3);
lean_inc_ref(v_mctxAfter_2635_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 3, v_mctxAfter_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_env_2625_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_cmdEnv_x3f_2626_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_fileMap_2627_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_mctxAfter_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_options_2628_);
lean_ctor_set(v_reuseFailAlloc_2644_, 5, v_currNamespace_2629_);
lean_ctor_set(v_reuseFailAlloc_2644_, 6, v_openDecls_2630_);
lean_ctor_set(v_reuseFailAlloc_2644_, 7, v_ngen_2631_);
v___x_2637_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2637_);
v___x_2639_ = v___x_2623_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_parentDecl_x3f_2620_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_autoImplicits_2621_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2639_);
v___x_2641_ = v___x_2616_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
}
else
{
return v_x_2612_;
}
}
else
{
return v_x_2612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_updateContext_x3f___boxed(lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2650_, v_x_2651_);
lean_dec_ref(v_x_2651_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_2653_, lean_object* v_x_2654_){
_start:
{
if (lean_obj_tag(v_x_2654_) == 0)
{
return v_x_2653_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_head_2655_ = lean_ctor_get(v_x_2654_, 0);
v_tail_2656_ = lean_ctor_get(v_x_2654_, 1);
v___x_2657_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_2658_ = lean_string_append(v_x_2653_, v___x_2657_);
v___x_2659_ = lean_expr_dbg_to_string(v_head_2655_);
v___x_2660_ = lean_string_append(v___x_2658_, v___x_2659_);
lean_dec_ref(v___x_2659_);
v_x_2653_ = v___x_2660_;
v_x_2654_ = v_tail_2656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_2662_, v_x_2663_);
lean_dec(v_x_2663_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_2668_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
lean_object* v___x_2669_; 
v___x_2669_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_2669_;
}
else
{
lean_object* v_tail_2670_; 
v_tail_2670_ = lean_ctor_get(v_x_2668_, 1);
if (lean_obj_tag(v_tail_2670_) == 0)
{
lean_object* v_head_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_head_2671_ = lean_ctor_get(v_x_2668_, 0);
v___x_2672_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2673_ = lean_expr_dbg_to_string(v_head_2671_);
v___x_2674_ = lean_string_append(v___x_2672_, v___x_2673_);
lean_dec_ref(v___x_2673_);
v___x_2675_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2676_ = lean_string_append(v___x_2674_, v___x_2675_);
return v___x_2676_;
}
else
{
lean_object* v_head_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint32_t v___x_2682_; lean_object* v___x_2683_; 
v_head_2677_ = lean_ctor_get(v_x_2668_, 0);
v___x_2678_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_2679_ = lean_expr_dbg_to_string(v_head_2677_);
v___x_2680_ = lean_string_append(v___x_2678_, v___x_2679_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_2680_, v_tail_2670_);
v___x_2682_ = 93;
v___x_2683_ = lean_string_push(v___x_2681_, v___x_2682_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_2684_);
lean_dec(v_x_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_2692_){
_start:
{
switch(lean_obj_tag(v_ctx_2692_))
{
case 0:
{
lean_object* v___x_2693_; 
lean_dec_ref(v_ctx_2692_);
v___x_2693_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_2693_;
}
case 1:
{
lean_object* v_parentDecl_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2707_; 
v_parentDecl_2694_ = lean_ctor_get(v_ctx_2692_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_ctx_2692_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2696_ = v_ctx_2692_;
v_isShared_2697_ = v_isSharedCheck_2707_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_parentDecl_2694_);
lean_dec(v_ctx_2692_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2707_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2698_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_2699_ = 1;
v___x_2700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_2694_, v___x_2699_);
v___x_2701_ = lean_string_append(v___x_2698_, v___x_2700_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2703_ = lean_string_append(v___x_2701_, v___x_2702_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 3);
lean_ctor_set(v___x_2696_, 0, v___x_2703_);
v___x_2705_ = v___x_2696_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
default: 
{
lean_object* v_autoImplicits_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2723_; 
v_autoImplicits_2708_ = lean_ctor_get(v_ctx_2692_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_ctx_2692_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2710_ = v_ctx_2692_;
v_isShared_2711_ = v_isSharedCheck_2723_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_autoImplicits_2708_);
lean_dec(v_ctx_2692_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2723_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2712_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_2713_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_2714_ = lean_array_to_list(v_autoImplicits_2708_);
v___x_2715_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_2714_);
lean_dec(v___x_2714_);
v___x_2716_ = lean_string_append(v___x_2713_, v___x_2715_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = lean_string_append(v___x_2712_, v___x_2716_);
lean_dec_ref(v___x_2716_);
v___x_2718_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__2));
v___x_2719_ = lean_string_append(v___x_2717_, v___x_2718_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 3);
lean_ctor_set(v___x_2710_, 0, v___x_2719_);
v___x_2721_ = v___x_2710_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(3, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_2733_, lean_object* v_ctx_x3f_2734_){
_start:
{
switch(lean_obj_tag(v_tree_2733_))
{
case 0:
{
lean_object* v_i_2736_; lean_object* v_t_2737_; lean_object* v___x_2738_; 
v_i_2736_ = lean_ctor_get(v_tree_2733_, 0);
lean_inc_ref(v_i_2736_);
v_t_2737_ = lean_ctor_get(v_tree_2733_, 1);
lean_inc_ref(v_t_2737_);
lean_dec_ref(v_tree_2733_);
v___x_2738_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2736_, v_ctx_x3f_2734_);
v_tree_2733_ = v_t_2737_;
v_ctx_x3f_2734_ = v___x_2738_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_2734_) == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec_ref(v_tree_2733_);
v___x_2740_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
else
{
lean_object* v_i_2742_; lean_object* v_children_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2793_; 
v_i_2742_ = lean_ctor_get(v_tree_2733_, 0);
v_children_2743_ = lean_ctor_get(v_tree_2733_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_tree_2733_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2745_ = v_tree_2733_;
v_isShared_2746_ = v_isSharedCheck_2793_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_children_2743_);
lean_inc(v_i_2742_);
lean_dec(v_tree_2733_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2793_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_val_2747_; lean_object* v___x_2748_; 
v_val_2747_ = lean_ctor_get(v_ctx_x3f_2734_, 0);
lean_inc_ref(v_i_2742_);
lean_inc(v_val_2747_);
v___x_2748_ = l_Lean_Elab_Info_format(v_val_2747_, v_i_2742_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2792_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2792_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2792_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_size_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_size_2753_ = lean_ctor_get(v_children_2743_, 2);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_nat_dec_eq(v_size_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2751_);
v___x_2756_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2734_, v_i_2742_);
lean_dec_ref(v_i_2742_);
v___x_2757_ = l_Lean_PersistentArray_toList___redArg(v_children_2743_);
lean_dec_ref(v_children_2743_);
v___x_2758_ = lean_box(0);
v___x_2759_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2756_, v___x_2757_, v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2775_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2775_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2775_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 5);
lean_ctor_set(v___x_2745_, 1, v_a_2749_);
lean_ctor_set(v___x_2745_, 0, v___x_2764_);
v___x_2766_ = v___x_2745_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_a_2749_);
v___x_2766_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2767_ = lean_box(1);
v___x_2768_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_2767_, v_a_2760_);
v___x_2769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Std_Format_nestD(v___x_2769_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2770_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2749_);
lean_del_object(v___x_2745_);
v_a_2776_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2759_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2759_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
lean_dec_ref(v_children_2743_);
lean_dec_ref(v_i_2742_);
lean_dec_ref(v_ctx_x3f_2734_);
v___x_2784_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 5);
lean_ctor_set(v___x_2745_, 1, v_a_2749_);
lean_ctor_set(v___x_2745_, 0, v___x_2784_);
v___x_2786_ = v___x_2745_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_a_2749_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = l_Std_Format_nestD(v___x_2786_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2787_);
v___x_2789_ = v___x_2751_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
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
}
else
{
lean_del_object(v___x_2745_);
lean_dec_ref(v_children_2743_);
lean_dec_ref(v_i_2742_);
lean_dec_ref(v_ctx_x3f_2734_);
return v___x_2748_;
}
}
}
}
default: 
{
lean_object* v_mvarId_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_ctx_x3f_2734_);
v_mvarId_2794_ = lean_ctor_get(v_tree_2733_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_tree_2733_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2796_ = v_tree_2733_;
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_mvarId_2794_);
lean_dec(v_tree_2733_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2798_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_2799_ = 1;
v___x_2800_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2794_, v___x_2799_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set_tag(v___x_2796_, 3);
lean_ctor_set(v___x_2796_, 0, v___x_2800_);
v___x_2802_ = v___x_2796_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2798_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = l_Std_Format_nestD(v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec(v___x_2808_);
v___x_2812_ = l_List_reverse___redArg(v_x_2810_);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
else
{
lean_object* v_head_2814_; lean_object* v_tail_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2833_; 
v_head_2814_ = lean_ctor_get(v_x_2809_, 0);
v_tail_2815_ = lean_ctor_get(v_x_2809_, 1);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2817_ = v_x_2809_;
v_isShared_2818_ = v_isSharedCheck_2833_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_tail_2815_);
lean_inc(v_head_2814_);
lean_dec(v_x_2809_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2833_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; 
lean_inc(v___x_2808_);
v___x_2819_ = l_Lean_Elab_InfoTree_format(v_head_2814_, v___x_2808_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v_x_2810_);
lean_ctor_set(v___x_2817_, 0, v_a_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2820_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_x_2810_);
v___x_2822_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
v_x_2809_ = v_tail_2815_;
v_x_2810_ = v___x_2822_;
goto _start;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_del_object(v___x_2817_);
lean_dec(v_tail_2815_);
lean_dec(v_x_2810_);
lean_dec(v___x_2808_);
v_a_2825_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2819_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2819_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_2834_, lean_object* v_x_2835_, lean_object* v_x_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_2834_, v_x_2835_, v_x_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_2839_, lean_object* v_ctx_x3f_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_Elab_InfoTree_format(v_tree_2839_, v_ctx_x3f_2840_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_2843_, lean_object* v_s_2844_){
_start:
{
uint8_t v_enabled_2845_; lean_object* v_assignment_2846_; lean_object* v_lazyAssignment_2847_; lean_object* v_trees_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2856_; 
v_enabled_2845_ = lean_ctor_get_uint8(v_s_2844_, sizeof(void*)*3);
v_assignment_2846_ = lean_ctor_get(v_s_2844_, 0);
v_lazyAssignment_2847_ = lean_ctor_get(v_s_2844_, 1);
v_trees_2848_ = lean_ctor_get(v_s_2844_, 2);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_s_2844_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2850_ = v_s_2844_;
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_trees_2848_);
lean_inc(v_lazyAssignment_2847_);
lean_inc(v_assignment_2846_);
lean_dec(v_s_2844_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2852_ = lean_apply_1(v_f_2843_, v_trees_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 2, v___x_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_assignment_2846_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_lazyAssignment_2847_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v___x_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2855_, sizeof(void*)*3, v_enabled_2845_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_2857_, lean_object* v_f_2858_){
_start:
{
lean_object* v_modifyInfoState_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v_modifyInfoState_2859_ = lean_ctor_get(v_inst_2857_, 1);
lean_inc(v_modifyInfoState_2859_);
lean_dec_ref(v_inst_2857_);
v___f_2860_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2860_, 0, v_f_2858_);
v___x_2861_ = lean_apply_1(v_modifyInfoState_2859_, v___f_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_2862_, lean_object* v_inst_2863_, lean_object* v_f_2864_){
_start:
{
lean_object* v_modifyInfoState_2865_; lean_object* v___f_2866_; lean_object* v___x_2867_; 
v_modifyInfoState_2865_ = lean_ctor_get(v_inst_2863_, 1);
lean_inc(v_modifyInfoState_2865_);
lean_dec_ref(v_inst_2863_);
v___f_2866_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2866_, 0, v_f_2864_);
v___x_2867_ = lean_apply_1(v_modifyInfoState_2865_, v___f_2866_);
return v___x_2867_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(32u);
v___x_2869_ = lean_mk_empty_array_with_capacity(v___x_2868_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2871_ = ((size_t)5ULL);
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_unsigned_to_nat(32u);
v___x_2874_ = lean_mk_empty_array_with_capacity(v___x_2873_);
v___x_2875_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_2876_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
lean_ctor_set(v___x_2876_, 2, v___x_2872_);
lean_ctor_set(v___x_2876_, 3, v___x_2872_);
lean_ctor_set_usize(v___x_2876_, 4, v___x_2871_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_2877_){
_start:
{
uint8_t v_enabled_2878_; lean_object* v_assignment_2879_; lean_object* v_lazyAssignment_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2888_; 
v_enabled_2878_ = lean_ctor_get_uint8(v_s_2877_, sizeof(void*)*3);
v_assignment_2879_ = lean_ctor_get(v_s_2877_, 0);
v_lazyAssignment_2880_ = lean_ctor_get(v_s_2877_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_s_2877_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; 
v_unused_2889_ = lean_ctor_get(v_s_2877_, 2);
lean_dec(v_unused_2889_);
v___x_2882_ = v_s_2877_;
v_isShared_2883_ = v_isSharedCheck_2888_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_lazyAssignment_2880_);
lean_inc(v_assignment_2879_);
lean_dec(v_s_2877_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2888_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2884_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 2, v___x_2884_);
v___x_2886_ = v___x_2882_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_assignment_2879_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_lazyAssignment_2880_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v___x_2884_);
lean_ctor_set_uint8(v_reuseFailAlloc_2887_, sizeof(void*)*3, v_enabled_2878_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2890_, lean_object* v_trees_2891_, lean_object* v_____r_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_apply_2(v_toPure_2890_, lean_box(0), v_trees_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2894_, lean_object* v_modifyInfoState_2895_, lean_object* v___f_2896_, lean_object* v_toBind_2897_, lean_object* v_____do__lift_2898_){
_start:
{
lean_object* v_trees_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_trees_2899_ = lean_ctor_get(v_____do__lift_2898_, 2);
lean_inc_ref(v_trees_2899_);
lean_dec_ref(v_____do__lift_2898_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2900_, 0, v_toPure_2894_);
lean_closure_set(v___f_2900_, 1, v_trees_2899_);
v___x_2901_ = lean_apply_1(v_modifyInfoState_2895_, v___f_2896_);
v___x_2902_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___x_2901_, v___f_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2904_, lean_object* v_inst_2905_){
_start:
{
lean_object* v_toApplicative_2906_; lean_object* v_toBind_2907_; lean_object* v_getInfoState_2908_; lean_object* v_modifyInfoState_2909_; lean_object* v_toPure_2910_; lean_object* v___f_2911_; lean_object* v___f_2912_; lean_object* v___x_2913_; 
v_toApplicative_2906_ = lean_ctor_get(v_inst_2904_, 0);
lean_inc_ref(v_toApplicative_2906_);
v_toBind_2907_ = lean_ctor_get(v_inst_2904_, 1);
lean_inc(v_toBind_2907_);
lean_dec_ref(v_inst_2904_);
v_getInfoState_2908_ = lean_ctor_get(v_inst_2905_, 0);
lean_inc(v_getInfoState_2908_);
v_modifyInfoState_2909_ = lean_ctor_get(v_inst_2905_, 1);
lean_inc(v_modifyInfoState_2909_);
lean_dec_ref(v_inst_2905_);
v_toPure_2910_ = lean_ctor_get(v_toApplicative_2906_, 1);
lean_inc(v_toPure_2910_);
lean_dec_ref(v_toApplicative_2906_);
v___f_2911_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
lean_inc(v_toBind_2907_);
v___f_2912_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2912_, 0, v_toPure_2910_);
lean_closure_set(v___f_2912_, 1, v_modifyInfoState_2909_);
lean_closure_set(v___f_2912_, 2, v___f_2911_);
lean_closure_set(v___f_2912_, 3, v_toBind_2907_);
v___x_2913_ = lean_apply_4(v_toBind_2907_, lean_box(0), lean_box(0), v_getInfoState_2908_, v___f_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2914_, lean_object* v_inst_2915_, lean_object* v_inst_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2915_, v_inst_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2918_, lean_object* v_s_2919_){
_start:
{
uint8_t v_enabled_2920_; lean_object* v_assignment_2921_; lean_object* v_lazyAssignment_2922_; lean_object* v_trees_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
v_enabled_2920_ = lean_ctor_get_uint8(v_s_2919_, sizeof(void*)*3);
v_assignment_2921_ = lean_ctor_get(v_s_2919_, 0);
v_lazyAssignment_2922_ = lean_ctor_get(v_s_2919_, 1);
v_trees_2923_ = lean_ctor_get(v_s_2919_, 2);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_s_2919_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2925_ = v_s_2919_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_trees_2923_);
lean_inc(v_lazyAssignment_2922_);
lean_inc(v_assignment_2921_);
lean_dec(v_s_2919_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = l_Lean_PersistentArray_push___redArg(v_trees_2923_, v_t_2918_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 2, v___x_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_assignment_2921_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_lazyAssignment_2922_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v___x_2927_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*3, v_enabled_2920_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2932_, lean_object* v_modifyInfoState_2933_, lean_object* v___f_2934_, lean_object* v_____do__lift_2935_){
_start:
{
uint8_t v_enabled_2936_; 
v_enabled_2936_ = lean_ctor_get_uint8(v_____do__lift_2935_, sizeof(void*)*3);
if (v_enabled_2936_ == 0)
{
lean_object* v_toPure_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec_ref(v___f_2934_);
lean_dec(v_modifyInfoState_2933_);
v_toPure_2937_ = lean_ctor_get(v_toApplicative_2932_, 1);
lean_inc(v_toPure_2937_);
lean_dec_ref(v_toApplicative_2932_);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_apply_2(v_toPure_2937_, lean_box(0), v___x_2938_);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; 
lean_dec_ref(v_toApplicative_2932_);
v___x_2940_ = lean_apply_1(v_modifyInfoState_2933_, v___f_2934_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_2941_, lean_object* v_modifyInfoState_2942_, lean_object* v___f_2943_, lean_object* v_____do__lift_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_2941_, v_modifyInfoState_2942_, v___f_2943_, v_____do__lift_2944_);
lean_dec_ref(v_____do__lift_2944_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_t_2948_){
_start:
{
lean_object* v_toApplicative_2949_; lean_object* v_toBind_2950_; lean_object* v_getInfoState_2951_; lean_object* v_modifyInfoState_2952_; lean_object* v___f_2953_; lean_object* v___f_2954_; lean_object* v___x_2955_; 
v_toApplicative_2949_ = lean_ctor_get(v_inst_2946_, 0);
lean_inc_ref(v_toApplicative_2949_);
v_toBind_2950_ = lean_ctor_get(v_inst_2946_, 1);
lean_inc(v_toBind_2950_);
lean_dec_ref(v_inst_2946_);
v_getInfoState_2951_ = lean_ctor_get(v_inst_2947_, 0);
lean_inc(v_getInfoState_2951_);
v_modifyInfoState_2952_ = lean_ctor_get(v_inst_2947_, 1);
lean_inc(v_modifyInfoState_2952_);
lean_dec_ref(v_inst_2947_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2953_, 0, v_t_2948_);
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2954_, 0, v_toApplicative_2949_);
lean_closure_set(v___f_2954_, 1, v_modifyInfoState_2952_);
lean_closure_set(v___f_2954_, 2, v___f_2953_);
v___x_2955_ = lean_apply_4(v_toBind_2950_, lean_box(0), lean_box(0), v_getInfoState_2951_, v___f_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_t_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2957_, v_inst_2958_, v_t_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_2961_, lean_object* v_t_2962_, lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_____do__lift_2965_){
_start:
{
uint8_t v_enabled_2966_; 
v_enabled_2966_ = lean_ctor_get_uint8(v_____do__lift_2965_, sizeof(void*)*3);
if (v_enabled_2966_ == 0)
{
lean_object* v_toPure_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v_inst_2964_);
lean_dec_ref(v_inst_2963_);
lean_dec_ref(v_t_2962_);
v_toPure_2967_ = lean_ctor_get(v_toApplicative_2961_, 1);
lean_inc(v_toPure_2967_);
lean_dec_ref(v_toApplicative_2961_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_apply_2(v_toPure_2967_, lean_box(0), v___x_2968_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v_toApplicative_2961_);
v___x_2970_ = lean_unsigned_to_nat(32u);
v___x_2971_ = lean_mk_empty_array_with_capacity(v___x_2970_);
lean_dec_ref(v___x_2971_);
v___x_2972_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_t_2962_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2963_, v_inst_2964_, v___x_2973_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_2975_, lean_object* v_t_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_____do__lift_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_2975_, v_t_2976_, v_inst_2977_, v_inst_2978_, v_____do__lift_2979_);
lean_dec_ref(v_____do__lift_2979_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_t_2983_){
_start:
{
lean_object* v_toApplicative_2984_; lean_object* v_toBind_2985_; lean_object* v_getInfoState_2986_; lean_object* v___f_2987_; lean_object* v___x_2988_; 
v_toApplicative_2984_ = lean_ctor_get(v_inst_2981_, 0);
lean_inc_ref(v_toApplicative_2984_);
v_toBind_2985_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_2985_);
v_getInfoState_2986_ = lean_ctor_get(v_inst_2982_, 0);
lean_inc(v_getInfoState_2986_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2987_, 0, v_toApplicative_2984_);
lean_closure_set(v___f_2987_, 1, v_t_2983_);
lean_closure_set(v___f_2987_, 2, v_inst_2981_);
lean_closure_set(v___f_2987_, 3, v_inst_2982_);
v___x_2988_ = lean_apply_4(v_toBind_2985_, lean_box(0), lean_box(0), v_getInfoState_2986_, v___f_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2989_, lean_object* v_inst_2990_, lean_object* v_inst_2991_, lean_object* v_t_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2990_, v_inst_2991_, v_t_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2994_, lean_object* v_inst_2995_, lean_object* v_info_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_info_2996_);
v___x_2998_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2994_, v_inst_2995_, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_info_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_3000_, v_inst_3001_, v_info_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_3004_, lean_object* v_expectedType_x3f_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_____do__lift_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_stx_3004_);
v___x_3011_ = l_Lean_LocalContext_empty;
v___x_3012_ = 0;
v___x_3013_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3013_, 0, v___x_3010_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
lean_ctor_set(v___x_3013_, 2, v_expectedType_x3f_3005_);
lean_ctor_set(v___x_3013_, 3, v_____do__lift_3008_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*4, v___x_3012_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*4 + 1, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
v___x_3015_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3006_, v_inst_3007_, v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_stx_3020_, lean_object* v_n_3021_, lean_object* v_expectedType_x3f_3022_){
_start:
{
lean_object* v_toBind_3023_; lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_toBind_3023_ = lean_ctor_get(v_inst_3016_, 1);
lean_inc(v_toBind_3023_);
lean_inc_ref(v_inst_3016_);
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3024_, 0, v_stx_3020_);
lean_closure_set(v___f_3024_, 1, v_expectedType_x3f_3022_);
lean_closure_set(v___f_3024_, 2, v_inst_3016_);
lean_closure_set(v___f_3024_, 3, v_inst_3017_);
v___x_3025_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_3016_, v_inst_3018_, v_inst_3019_, v_n_3021_);
v___x_3026_ = lean_apply_4(v_toBind_3023_, lean_box(0), lean_box(0), v___x_3025_, v___f_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_3027_, lean_object* v_inst_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_stx_3032_, lean_object* v_n_3033_, lean_object* v_expectedType_x3f_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Elab_addConstInfo___redArg(v_inst_3028_, v_inst_3029_, v_inst_3030_, v_inst_3031_, v_stx_3032_, v_n_3033_, v_expectedType_x3f_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v_infoState_3040_; uint8_t v_enabled_3041_; 
v___x_3039_ = lean_st_ref_get(v___y_3037_);
v_infoState_3040_ = lean_ctor_get(v___x_3039_, 7);
lean_inc_ref(v_infoState_3040_);
lean_dec(v___x_3039_);
v_enabled_3041_ = lean_ctor_get_uint8(v_infoState_3040_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3040_);
if (v_enabled_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_dec_ref(v_t_3036_);
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
else
{
lean_object* v___x_3044_; lean_object* v_infoState_3045_; lean_object* v_env_3046_; lean_object* v_nextMacroScope_3047_; lean_object* v_ngen_3048_; lean_object* v_auxDeclNGen_3049_; lean_object* v_traceState_3050_; lean_object* v_cache_3051_; lean_object* v_messages_3052_; lean_object* v_snapshotTasks_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3075_; 
v___x_3044_ = lean_st_ref_take(v___y_3037_);
v_infoState_3045_ = lean_ctor_get(v___x_3044_, 7);
v_env_3046_ = lean_ctor_get(v___x_3044_, 0);
v_nextMacroScope_3047_ = lean_ctor_get(v___x_3044_, 1);
v_ngen_3048_ = lean_ctor_get(v___x_3044_, 2);
v_auxDeclNGen_3049_ = lean_ctor_get(v___x_3044_, 3);
v_traceState_3050_ = lean_ctor_get(v___x_3044_, 4);
v_cache_3051_ = lean_ctor_get(v___x_3044_, 5);
v_messages_3052_ = lean_ctor_get(v___x_3044_, 6);
v_snapshotTasks_3053_ = lean_ctor_get(v___x_3044_, 8);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3055_ = v___x_3044_;
v_isShared_3056_ = v_isSharedCheck_3075_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_snapshotTasks_3053_);
lean_inc(v_infoState_3045_);
lean_inc(v_messages_3052_);
lean_inc(v_cache_3051_);
lean_inc(v_traceState_3050_);
lean_inc(v_auxDeclNGen_3049_);
lean_inc(v_ngen_3048_);
lean_inc(v_nextMacroScope_3047_);
lean_inc(v_env_3046_);
lean_dec(v___x_3044_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3075_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
uint8_t v_enabled_3057_; lean_object* v_assignment_3058_; lean_object* v_lazyAssignment_3059_; lean_object* v_trees_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3074_; 
v_enabled_3057_ = lean_ctor_get_uint8(v_infoState_3045_, sizeof(void*)*3);
v_assignment_3058_ = lean_ctor_get(v_infoState_3045_, 0);
v_lazyAssignment_3059_ = lean_ctor_get(v_infoState_3045_, 1);
v_trees_3060_ = lean_ctor_get(v_infoState_3045_, 2);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_infoState_3045_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3062_ = v_infoState_3045_;
v_isShared_3063_ = v_isSharedCheck_3074_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_trees_3060_);
lean_inc(v_lazyAssignment_3059_);
lean_inc(v_assignment_3058_);
lean_dec(v_infoState_3045_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3074_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3064_ = l_Lean_PersistentArray_push___redArg(v_trees_3060_, v_t_3036_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 2, v___x_3064_);
v___x_3066_ = v___x_3062_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_assignment_3058_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_lazyAssignment_3059_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v___x_3064_);
lean_ctor_set_uint8(v_reuseFailAlloc_3073_, sizeof(void*)*3, v_enabled_3057_);
v___x_3066_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 7, v___x_3066_);
v___x_3068_ = v___x_3055_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_env_3046_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_nextMacroScope_3047_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ngen_3048_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_auxDeclNGen_3049_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_traceState_3050_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v_cache_3051_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_messages_3052_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_snapshotTasks_3053_);
v___x_3068_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_st_ref_set(v___y_3037_, v___x_3068_);
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3076_, v___y_3077_);
lean_dec(v___y_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v_infoState_3085_; uint8_t v_enabled_3086_; 
v___x_3084_ = lean_st_ref_get(v___y_3082_);
v_infoState_3085_ = lean_ctor_get(v___x_3084_, 7);
lean_inc_ref(v_infoState_3085_);
lean_dec(v___x_3084_);
v_enabled_3086_ = lean_ctor_get_uint8(v_infoState_3085_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3085_);
if (v_enabled_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v_t_3080_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3089_ = lean_unsigned_to_nat(32u);
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_3089_);
lean_dec_ref(v___x_3090_);
v___x_3091_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_3092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_t_3080_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_3092_, v___y_3082_);
return v___x_3093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
return v_res_3098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
lean_ctor_set(v___x_3104_, 2, v___x_3103_);
lean_ctor_set(v___x_3104_, 3, v___x_3102_);
lean_ctor_set(v___x_3104_, 4, v___x_3102_);
lean_ctor_set(v___x_3104_, 5, v___x_3102_);
lean_ctor_set(v___x_3104_, 6, v___x_3102_);
lean_ctor_set(v___x_3104_, 7, v___x_3102_);
lean_ctor_set(v___x_3104_, 8, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = lean_box(1);
v___x_3106_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_3107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_3108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
lean_ctor_set(v___x_3108_, 1, v___x_3106_);
lean_ctor_set(v___x_3108_, 2, v___x_3105_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_3111_ = l_Lean_stringToMessageData(v___x_3110_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_3114_ = l_Lean_stringToMessageData(v___x_3113_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_3117_ = l_Lean_stringToMessageData(v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_3120_ = l_Lean_stringToMessageData(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_3123_ = l_Lean_stringToMessageData(v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_3130_, lean_object* v_declHint_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; lean_object* v_env_3135_; uint8_t v___x_3136_; 
v___x_3134_ = lean_st_ref_get(v___y_3132_);
v_env_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_ref(v_env_3135_);
lean_dec(v___x_3134_);
v___x_3136_ = l_Lean_Name_isAnonymous(v_declHint_3131_);
if (v___x_3136_ == 0)
{
uint8_t v_isExporting_3137_; 
v_isExporting_3137_ = lean_ctor_get_uint8(v_env_3135_, sizeof(void*)*8);
if (v_isExporting_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec_ref(v_env_3135_);
lean_dec(v_declHint_3131_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_msg_3130_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
lean_inc_ref(v_env_3135_);
v___x_3139_ = l_Lean_Environment_setExporting(v_env_3135_, v___x_3136_);
lean_inc(v_declHint_3131_);
lean_inc_ref(v___x_3139_);
v___x_3140_ = l_Lean_Environment_contains(v___x_3139_, v_declHint_3131_, v_isExporting_3137_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; 
lean_dec_ref(v___x_3139_);
lean_dec_ref(v_env_3135_);
lean_dec(v_declHint_3131_);
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v_msg_3130_);
return v___x_3141_;
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_c_3147_; lean_object* v___x_3148_; 
v___x_3142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_3144_ = l_Lean_Options_empty;
v___x_3145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3139_);
lean_ctor_set(v___x_3145_, 1, v___x_3142_);
lean_ctor_set(v___x_3145_, 2, v___x_3143_);
lean_ctor_set(v___x_3145_, 3, v___x_3144_);
lean_inc(v_declHint_3131_);
v___x_3146_ = l_Lean_MessageData_ofConstName(v_declHint_3131_, v___x_3136_);
v_c_3147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3147_, 0, v___x_3145_);
lean_ctor_set(v_c_3147_, 1, v___x_3146_);
v___x_3148_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3135_, v_declHint_3131_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec_ref(v_env_3135_);
lean_dec(v_declHint_3131_);
v___x_3149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v_c_3147_);
v___x_3151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_MessageData_note(v___x_3152_);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_msg_3130_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
else
{
lean_object* v_val_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3191_; 
v_val_3156_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3158_ = v___x_3148_;
v_isShared_3159_ = v_isSharedCheck_3191_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_val_3156_);
lean_dec(v___x_3148_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3191_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_mod_3163_; uint8_t v___x_3164_; 
v___x_3160_ = lean_box(0);
v___x_3161_ = l_Lean_Environment_header(v_env_3135_);
lean_dec_ref(v_env_3135_);
v___x_3162_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3161_);
v_mod_3163_ = lean_array_get(v___x_3160_, v___x_3162_, v_val_3156_);
lean_dec(v_val_3156_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = l_Lean_isPrivateName(v_declHint_3131_);
lean_dec(v_declHint_3131_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v_c_3147_);
v___x_3167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_MessageData_ofName(v_mod_3163_);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_MessageData_note(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_msg_3130_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3174_);
v___x_3176_ = v___x_3158_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_c_3147_);
v___x_3180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_MessageData_ofName(v_mod_3163_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Lean_MessageData_note(v___x_3185_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_msg_3130_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3187_);
v___x_3189_ = v___x_3158_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3192_; 
lean_dec_ref(v_env_3135_);
lean_dec(v_declHint_3131_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_msg_3130_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_3193_, lean_object* v_declHint_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3193_, v_declHint_3194_, v___y_3195_);
lean_dec(v___y_3195_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_3198_, lean_object* v_declHint_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3213_; 
v___x_3203_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3198_, v_declHint_3199_, v___y_3201_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3208_ = l_Lean_unknownIdentifierMessageTag;
v___x_3209_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v_a_3204_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3209_);
v___x_3211_ = v___x_3206_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_3214_, lean_object* v_declHint_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3214_, v_declHint_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; lean_object* v_env_3225_; lean_object* v_options_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3224_ = lean_st_ref_get(v___y_3222_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
v_options_3226_ = lean_ctor_get(v___y_3221_, 2);
v___x_3227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_3228_ = lean_unsigned_to_nat(32u);
v___x_3229_ = lean_mk_empty_array_with_capacity(v___x_3228_);
lean_dec_ref(v___x_3229_);
v___x_3230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_3226_);
v___x_3231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3231_, 0, v_env_3225_);
lean_ctor_set(v___x_3231_, 1, v___x_3227_);
lean_ctor_set(v___x_3231_, 2, v___x_3230_);
lean_ctor_set(v___x_3231_, 3, v_options_3226_);
v___x_3232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_msgData_3220_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_ref_3243_; lean_object* v___x_3244_; lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3253_; 
v_ref_3243_ = lean_ctor_get(v___y_3240_, 5);
v___x_3244_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_3239_, v___y_3240_, v___y_3241_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3253_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3253_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
lean_inc(v_ref_3243_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_ref_3243_);
lean_ctor_set(v___x_3249_, 1, v_a_3245_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set_tag(v___x_3247_, 1);
lean_ctor_set(v___x_3247_, 0, v___x_3249_);
v___x_3251_ = v___x_3247_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_3259_, lean_object* v_msg_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_fileName_3264_; lean_object* v_fileMap_3265_; lean_object* v_options_3266_; lean_object* v_currRecDepth_3267_; lean_object* v_maxRecDepth_3268_; lean_object* v_ref_3269_; lean_object* v_currNamespace_3270_; lean_object* v_openDecls_3271_; lean_object* v_initHeartbeats_3272_; lean_object* v_maxHeartbeats_3273_; lean_object* v_quotContext_3274_; lean_object* v_currMacroScope_3275_; uint8_t v_diag_3276_; lean_object* v_cancelTk_x3f_3277_; uint8_t v_suppressElabErrors_3278_; lean_object* v_inheritedTraceOptions_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3288_; 
v_fileName_3264_ = lean_ctor_get(v___y_3261_, 0);
v_fileMap_3265_ = lean_ctor_get(v___y_3261_, 1);
v_options_3266_ = lean_ctor_get(v___y_3261_, 2);
v_currRecDepth_3267_ = lean_ctor_get(v___y_3261_, 3);
v_maxRecDepth_3268_ = lean_ctor_get(v___y_3261_, 4);
v_ref_3269_ = lean_ctor_get(v___y_3261_, 5);
v_currNamespace_3270_ = lean_ctor_get(v___y_3261_, 6);
v_openDecls_3271_ = lean_ctor_get(v___y_3261_, 7);
v_initHeartbeats_3272_ = lean_ctor_get(v___y_3261_, 8);
v_maxHeartbeats_3273_ = lean_ctor_get(v___y_3261_, 9);
v_quotContext_3274_ = lean_ctor_get(v___y_3261_, 10);
v_currMacroScope_3275_ = lean_ctor_get(v___y_3261_, 11);
v_diag_3276_ = lean_ctor_get_uint8(v___y_3261_, sizeof(void*)*14);
v_cancelTk_x3f_3277_ = lean_ctor_get(v___y_3261_, 12);
v_suppressElabErrors_3278_ = lean_ctor_get_uint8(v___y_3261_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3279_ = lean_ctor_get(v___y_3261_, 13);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___y_3261_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3281_ = v___y_3261_;
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_inheritedTraceOptions_3279_);
lean_inc(v_cancelTk_x3f_3277_);
lean_inc(v_currMacroScope_3275_);
lean_inc(v_quotContext_3274_);
lean_inc(v_maxHeartbeats_3273_);
lean_inc(v_initHeartbeats_3272_);
lean_inc(v_openDecls_3271_);
lean_inc(v_currNamespace_3270_);
lean_inc(v_ref_3269_);
lean_inc(v_maxRecDepth_3268_);
lean_inc(v_currRecDepth_3267_);
lean_inc(v_options_3266_);
lean_inc(v_fileMap_3265_);
lean_inc(v_fileName_3264_);
lean_dec(v___y_3261_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_ref_3283_; lean_object* v___x_3285_; 
v_ref_3283_ = l_Lean_replaceRef(v_ref_3259_, v_ref_3269_);
lean_dec(v_ref_3269_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 5, v_ref_3283_);
v___x_3285_ = v___x_3281_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_fileName_3264_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_fileMap_3265_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_options_3266_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_currRecDepth_3267_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_maxRecDepth_3268_);
lean_ctor_set(v_reuseFailAlloc_3287_, 5, v_ref_3283_);
lean_ctor_set(v_reuseFailAlloc_3287_, 6, v_currNamespace_3270_);
lean_ctor_set(v_reuseFailAlloc_3287_, 7, v_openDecls_3271_);
lean_ctor_set(v_reuseFailAlloc_3287_, 8, v_initHeartbeats_3272_);
lean_ctor_set(v_reuseFailAlloc_3287_, 9, v_maxHeartbeats_3273_);
lean_ctor_set(v_reuseFailAlloc_3287_, 10, v_quotContext_3274_);
lean_ctor_set(v_reuseFailAlloc_3287_, 11, v_currMacroScope_3275_);
lean_ctor_set(v_reuseFailAlloc_3287_, 12, v_cancelTk_x3f_3277_);
lean_ctor_set(v_reuseFailAlloc_3287_, 13, v_inheritedTraceOptions_3279_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, sizeof(void*)*14, v_diag_3276_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, sizeof(void*)*14 + 1, v_suppressElabErrors_3278_);
v___x_3285_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3260_, v___x_3285_, v___y_3262_);
lean_dec_ref(v___x_3285_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3289_, lean_object* v_msg_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3289_, v_msg_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec(v_ref_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_3295_, lean_object* v_msg_3296_, lean_object* v_declHint_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v_a_3302_; lean_object* v___x_3303_; 
v___x_3301_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_3296_, v_declHint_3297_, v___y_3298_, v___y_3299_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3295_, v_a_3302_, v___y_3298_, v___y_3299_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3304_, lean_object* v_msg_3305_, lean_object* v_declHint_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3304_, v_msg_3305_, v_declHint_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec(v_ref_3304_);
return v_res_3310_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_3317_, lean_object* v_constName_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3322_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3323_ = 0;
lean_inc(v_constName_3318_);
v___x_3324_ = l_Lean_MessageData_ofConstName(v_constName_3318_, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3322_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3317_, v___x_3327_, v_constName_3318_, v___y_3319_, v___y_3320_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_3329_, lean_object* v_constName_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3329_, v_constName_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec(v_ref_3329_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_ref_3339_; lean_object* v___x_3340_; 
v_ref_3339_ = lean_ctor_get(v___y_3336_, 5);
lean_inc(v_ref_3339_);
v___x_3340_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3339_, v_constName_3335_, v___y_3336_, v___y_3337_);
lean_dec(v_ref_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v_env_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3350_ = lean_st_ref_get(v___y_3348_);
v_env_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_env_3351_);
lean_dec(v___x_3350_);
v___x_3352_ = 0;
lean_inc(v_constName_3346_);
v___x_3353_ = l_Lean_Environment_findConstVal_x3f(v_env_3351_, v_constName_3346_, v___x_3352_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3346_, v___y_3347_, v___y_3348_);
return v___x_3354_;
}
else
{
lean_object* v_val_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v___y_3347_);
lean_dec(v_constName_3346_);
v_val_3355_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3353_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_val_3355_);
lean_dec(v___x_3353_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 0);
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_val_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
if (lean_obj_tag(v_a_3368_) == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = l_List_reverse___redArg(v_a_3369_);
return v___x_3370_;
}
else
{
lean_object* v_head_3371_; lean_object* v_tail_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3381_; 
v_head_3371_ = lean_ctor_get(v_a_3368_, 0);
v_tail_3372_ = lean_ctor_get(v_a_3368_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3374_ = v_a_3368_;
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_tail_3372_);
lean_inc(v_head_3371_);
lean_dec(v_a_3368_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = l_Lean_mkLevelParam(v_head_3371_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 1, v_a_3369_);
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3369_);
v___x_3378_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
v_a_3368_ = v_tail_3372_;
v_a_3369_ = v___x_3378_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
lean_inc(v_constName_3382_);
v___x_3386_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3398_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3398_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3398_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_levelParams_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v_levelParams_3391_ = lean_ctor_get(v_a_3387_, 1);
lean_inc(v_levelParams_3391_);
lean_dec(v_a_3387_);
v___x_3392_ = lean_box(0);
v___x_3393_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_3391_, v___x_3392_);
v___x_3394_ = l_Lean_mkConst(v_constName_3382_, v___x_3393_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3394_);
v___x_3396_ = v___x_3389_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_constName_3382_);
v_a_3399_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3386_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3386_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_3412_, lean_object* v_n_3413_, lean_object* v_expectedType_x3f_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
lean_inc_ref(v___y_3415_);
v___x_3418_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_3413_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v_stx_3412_);
v___x_3422_ = l_Lean_LocalContext_empty;
v___x_3423_ = 0;
v___x_3424_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3424_, 0, v___x_3421_);
lean_ctor_set(v___x_3424_, 1, v___x_3422_);
lean_ctor_set(v___x_3424_, 2, v_expectedType_x3f_3414_);
lean_ctor_set(v___x_3424_, 3, v_a_3419_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*4, v___x_3423_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*4 + 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
v___x_3426_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_3425_, v___y_3415_, v___y_3416_);
lean_dec_ref(v___y_3415_);
return v___x_3426_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v___y_3415_);
lean_dec(v_expectedType_x3f_3414_);
lean_dec(v_stx_3412_);
v_a_3427_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3418_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3418_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_3435_, lean_object* v_n_3436_, lean_object* v_expectedType_x3f_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_3435_, v_n_3436_, v_expectedType_x3f_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_3442_, lean_object* v_expectedType_x3f_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v___x_3447_; 
lean_inc(v_a_3445_);
lean_inc_ref(v_a_3444_);
lean_inc(v_id_3442_);
v___x_3447_ = l_Lean_realizeGlobalConstNoOverload(v_id_3442_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3475_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3475_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3475_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v_infoState_3453_; uint8_t v_enabled_3454_; 
v___x_3452_ = lean_st_ref_get(v_a_3445_);
v_infoState_3453_ = lean_ctor_get(v___x_3452_, 7);
lean_inc_ref(v_infoState_3453_);
lean_dec(v___x_3452_);
v_enabled_3454_ = lean_ctor_get_uint8(v_infoState_3453_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3453_);
if (v_enabled_3454_ == 0)
{
lean_object* v___x_3456_; 
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_expectedType_x3f_3443_);
lean_dec(v_id_3442_);
if (v_isShared_3451_ == 0)
{
v___x_3456_ = v___x_3450_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3448_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
else
{
lean_object* v___x_3458_; 
lean_del_object(v___x_3450_);
lean_inc(v_a_3448_);
v___x_3458_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3442_, v_a_3448_, v_expectedType_x3f_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3458_, 0);
lean_dec(v_unused_3466_);
v___x_3460_ = v___x_3458_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v___x_3458_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v_a_3448_);
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3448_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_a_3448_);
v_a_3467_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3458_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3458_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_expectedType_x3f_3443_);
lean_dec(v_id_3442_);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_3476_, lean_object* v_expectedType_x3f_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3476_, v_expectedType_x3f_3477_, v_a_3478_, v_a_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_3482_, v___y_3484_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3492_, lean_object* v_constName_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_3493_, v___y_3494_, v___y_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3498_, lean_object* v_constName_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3498_, v_constName_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_3504_, lean_object* v_ref_3505_, lean_object* v_constName_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_3505_, v_constName_3506_, v___y_3507_, v___y_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3511_, lean_object* v_ref_3512_, lean_object* v_constName_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_3511_, v_ref_3512_, v_constName_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec(v_ref_3512_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3518_, lean_object* v_ref_3519_, lean_object* v_msg_3520_, lean_object* v_declHint_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_3519_, v_msg_3520_, v_declHint_3521_, v___y_3522_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3526_, lean_object* v_ref_3527_, lean_object* v_msg_3528_, lean_object* v_declHint_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_3526_, v_ref_3527_, v_msg_3528_, v_declHint_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec(v_ref_3527_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_3534_, lean_object* v_declHint_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_3534_, v_declHint_3535_, v___y_3537_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_3540_, lean_object* v_declHint_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_3540_, v_declHint_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3546_, lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_3547_, v_msg_3548_, v___y_3549_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3553_, lean_object* v_ref_3554_, lean_object* v_msg_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_3553_, v_ref_3554_, v_msg_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec(v_ref_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_3560_, lean_object* v_msg_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_3561_, v___y_3562_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_msg_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_3566_, v_msg_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_3572_, lean_object* v_expectedType_x3f_3573_, lean_object* v_as_x27_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
if (lean_obj_tag(v_as_x27_3574_) == 0)
{
lean_object* v___x_3579_; 
lean_dec_ref(v___y_3576_);
lean_dec(v_expectedType_x3f_3573_);
lean_dec(v_id_3572_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v_b_3575_);
return v___x_3579_;
}
else
{
lean_object* v_head_3580_; lean_object* v_tail_3581_; lean_object* v___x_3582_; 
v_head_3580_ = lean_ctor_get(v_as_x27_3574_, 0);
lean_inc(v_head_3580_);
v_tail_3581_ = lean_ctor_get(v_as_x27_3574_, 1);
lean_inc(v_tail_3581_);
lean_dec_ref(v_as_x27_3574_);
lean_inc_ref(v___y_3576_);
lean_inc(v_expectedType_x3f_3573_);
lean_inc(v_id_3572_);
v___x_3582_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_3572_, v_head_3580_, v_expectedType_x3f_3573_, v___y_3576_, v___y_3577_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; 
lean_dec_ref(v___x_3582_);
v___x_3583_ = lean_box(0);
v_as_x27_3574_ = v_tail_3581_;
v_b_3575_ = v___x_3583_;
goto _start;
}
else
{
lean_dec(v_tail_3581_);
lean_dec_ref(v___y_3576_);
lean_dec(v_expectedType_x3f_3573_);
lean_dec(v_id_3572_);
return v___x_3582_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_3585_, lean_object* v_expectedType_x3f_3586_, lean_object* v_as_x27_3587_, lean_object* v_b_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3585_, v_expectedType_x3f_3586_, v_as_x27_3587_, v_b_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_3593_, lean_object* v_expectedType_x3f_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3598_; 
lean_inc(v_a_3596_);
lean_inc_ref(v_a_3595_);
lean_inc(v_id_3593_);
v___x_3598_ = l_Lean_realizeGlobalConst(v_id_3593_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3627_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3627_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3627_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v_infoState_3604_; uint8_t v_enabled_3605_; 
v___x_3603_ = lean_st_ref_get(v_a_3596_);
v_infoState_3604_ = lean_ctor_get(v___x_3603_, 7);
lean_inc_ref(v_infoState_3604_);
lean_dec(v___x_3603_);
v_enabled_3605_ = lean_ctor_get_uint8(v_infoState_3604_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3604_);
if (v_enabled_3605_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_expectedType_x3f_3594_);
lean_dec(v_id_3593_);
if (v_isShared_3602_ == 0)
{
v___x_3607_ = v___x_3601_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3599_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_del_object(v___x_3601_);
v___x_3609_ = lean_box(0);
lean_inc(v_a_3599_);
v___x_3610_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3593_, v_expectedType_x3f_3594_, v_a_3599_, v___x_3609_, v_a_3595_, v_a_3596_);
lean_dec(v_a_3596_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v___x_3610_, 0);
lean_dec(v_unused_3618_);
v___x_3612_ = v___x_3610_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_dec(v___x_3610_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v_a_3599_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3599_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v_a_3599_);
v_a_3619_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3610_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3610_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_expectedType_x3f_3594_);
lean_dec(v_id_3593_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_3628_, lean_object* v_expectedType_x3f_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_3628_, v_expectedType_x3f_3629_, v_a_3630_, v_a_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_3634_, lean_object* v_expectedType_x3f_3635_, lean_object* v_as_3636_, lean_object* v_as_x27_3637_, lean_object* v_b_3638_, lean_object* v_a_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_3634_, v_expectedType_x3f_3635_, v_as_x27_3637_, v_b_3638_, v___y_3640_, v___y_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_3644_, lean_object* v_expectedType_x3f_3645_, lean_object* v_as_3646_, lean_object* v_as_x27_3647_, lean_object* v_b_3648_, lean_object* v_a_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_3644_, v_expectedType_x3f_3645_, v_as_3646_, v_as_x27_3647_, v_b_3648_, v_a_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec(v_as_3646_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_3654_, lean_object* v_as_x27_3655_, lean_object* v_b_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
if (lean_obj_tag(v_as_x27_3655_) == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref(v___y_3657_);
lean_dec(v_ref_3654_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_b_3656_);
return v___x_3660_;
}
else
{
lean_object* v_head_3661_; lean_object* v_tail_3662_; lean_object* v_fst_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_head_3661_ = lean_ctor_get(v_as_x27_3655_, 0);
lean_inc(v_head_3661_);
v_tail_3662_ = lean_ctor_get(v_as_x27_3655_, 1);
lean_inc(v_tail_3662_);
lean_dec_ref(v_as_x27_3655_);
v_fst_3663_ = lean_ctor_get(v_head_3661_, 0);
lean_inc(v_fst_3663_);
lean_dec(v_head_3661_);
v___x_3664_ = lean_box(0);
lean_inc_ref(v___y_3657_);
lean_inc(v_ref_3654_);
v___x_3665_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_3654_, v_fst_3663_, v___x_3664_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3666_; 
lean_dec_ref(v___x_3665_);
v___x_3666_ = lean_box(0);
v_as_x27_3655_ = v_tail_3662_;
v_b_3656_ = v___x_3666_;
goto _start;
}
else
{
lean_dec(v_tail_3662_);
lean_dec_ref(v___y_3657_);
lean_dec(v_ref_3654_);
return v___x_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_3668_, lean_object* v_as_x27_3669_, lean_object* v_b_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3668_, v_as_x27_3669_, v_b_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_3675_, lean_object* v_id_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3680_; 
lean_inc(v_a_3678_);
lean_inc_ref(v_a_3677_);
v___x_3680_ = l_Lean_realizeGlobalName(v_id_3676_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3709_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3709_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3709_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v_infoState_3686_; uint8_t v_enabled_3687_; 
v___x_3685_ = lean_st_ref_get(v_a_3678_);
v_infoState_3686_ = lean_ctor_get(v___x_3685_, 7);
lean_inc_ref(v_infoState_3686_);
lean_dec(v___x_3685_);
v_enabled_3687_ = lean_ctor_get_uint8(v_infoState_3686_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3686_);
if (v_enabled_3687_ == 0)
{
lean_object* v___x_3689_; 
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_ref_3675_);
if (v_isShared_3684_ == 0)
{
v___x_3689_ = v___x_3683_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3681_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
lean_del_object(v___x_3683_);
v___x_3691_ = lean_box(0);
lean_inc(v_a_3681_);
v___x_3692_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3675_, v_a_3681_, v___x_3691_, v_a_3677_, v_a_3678_);
lean_dec(v_a_3678_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v___x_3692_, 0);
lean_dec(v_unused_3700_);
v___x_3694_ = v___x_3692_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v___x_3692_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v_a_3681_);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3681_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_a_3681_);
v_a_3701_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3692_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3692_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_ref_3675_);
return v___x_3680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_3710_, lean_object* v_id_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_3710_, v_id_3711_, v_a_3712_, v_a_3713_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_3716_, lean_object* v_as_3717_, lean_object* v_as_x27_3718_, lean_object* v_b_3719_, lean_object* v_a_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_3716_, v_as_x27_3718_, v_b_3719_, v___y_3721_, v___y_3722_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_3725_, lean_object* v_as_3726_, lean_object* v_as_x27_3727_, lean_object* v_b_3728_, lean_object* v_a_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_3725_, v_as_3726_, v_as_x27_3727_, v_b_3728_, v_a_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec(v_as_3726_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_3734_){
_start:
{
lean_object* v_fst_3735_; 
v_fst_3735_ = lean_ctor_get(v_self_3734_, 0);
lean_inc(v_fst_3735_);
return v_fst_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_3736_);
lean_dec_ref(v_self_3736_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_3738_, lean_object* v_treesSaved_3739_, lean_object* v_s_3740_){
_start:
{
if (lean_obj_tag(v_info_3738_) == 0)
{
uint8_t v_enabled_3741_; lean_object* v_assignment_3742_; lean_object* v_lazyAssignment_3743_; lean_object* v_trees_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3754_; 
v_enabled_3741_ = lean_ctor_get_uint8(v_s_3740_, sizeof(void*)*3);
v_assignment_3742_ = lean_ctor_get(v_s_3740_, 0);
v_lazyAssignment_3743_ = lean_ctor_get(v_s_3740_, 1);
v_trees_3744_ = lean_ctor_get(v_s_3740_, 2);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_s_3740_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3746_ = v_s_3740_;
v_isShared_3747_ = v_isSharedCheck_3754_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_trees_3744_);
lean_inc(v_lazyAssignment_3743_);
lean_inc(v_assignment_3742_);
lean_dec(v_s_3740_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3754_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_val_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v_val_3748_ = lean_ctor_get(v_info_3738_, 0);
lean_inc(v_val_3748_);
lean_dec_ref(v_info_3738_);
v___x_3749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3749_, 0, v_val_3748_);
lean_ctor_set(v___x_3749_, 1, v_trees_3744_);
v___x_3750_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3739_, v___x_3749_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 2, v___x_3750_);
v___x_3752_ = v___x_3746_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_assignment_3742_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_lazyAssignment_3743_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v___x_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3753_, sizeof(void*)*3, v_enabled_3741_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
uint8_t v_enabled_3755_; lean_object* v_assignment_3756_; lean_object* v_lazyAssignment_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3773_; 
v_enabled_3755_ = lean_ctor_get_uint8(v_s_3740_, sizeof(void*)*3);
v_assignment_3756_ = lean_ctor_get(v_s_3740_, 0);
v_lazyAssignment_3757_ = lean_ctor_get(v_s_3740_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_s_3740_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; 
v_unused_3774_ = lean_ctor_get(v_s_3740_, 2);
lean_dec(v_unused_3774_);
v___x_3759_ = v_s_3740_;
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_lazyAssignment_3757_);
lean_inc(v_assignment_3756_);
lean_dec(v_s_3740_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3772_; 
v_val_3761_ = lean_ctor_get(v_info_3738_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_info_3738_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3763_ = v_info_3738_;
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v_info_3738_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 2);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_val_3761_);
v___x_3766_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3739_, v___x_3766_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 2, v___x_3767_);
v___x_3769_ = v___x_3759_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_assignment_3756_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_lazyAssignment_3757_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v___x_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3770_, sizeof(void*)*3, v_enabled_3755_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_3775_, lean_object* v_modifyInfoState_3776_, lean_object* v_info_3777_){
_start:
{
lean_object* v___f_3778_; lean_object* v___x_3779_; 
v___f_3778_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3778_, 0, v_info_3777_);
lean_closure_set(v___f_3778_, 1, v_treesSaved_3775_);
v___x_3779_ = lean_apply_1(v_modifyInfoState_3776_, v___f_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_3780_, lean_object* v_info_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_apply_1(v___f_3780_, v_info_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_3783_, lean_object* v_toBind_3784_, lean_object* v___f_3785_, lean_object* v_____do__lift_3786_){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_____do__lift_3786_);
v___x_3788_ = lean_apply_2(v_toPure_3783_, lean_box(0), v___x_3787_);
v___x_3789_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3788_, v___f_3785_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_3790_, lean_object* v_mkInfoOnError_3791_, lean_object* v___f_3792_, lean_object* v_mkInfo_3793_, lean_object* v___f_3794_, lean_object* v_a_x3f_3795_){
_start:
{
if (lean_obj_tag(v_a_x3f_3795_) == 0)
{
lean_object* v___x_3796_; 
lean_dec(v___f_3794_);
lean_dec(v_mkInfo_3793_);
v___x_3796_ = lean_apply_4(v_toBind_3790_, lean_box(0), lean_box(0), v_mkInfoOnError_3791_, v___f_3792_);
return v___x_3796_;
}
else
{
lean_object* v_val_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec(v___f_3792_);
lean_dec(v_mkInfoOnError_3791_);
v_val_3797_ = lean_ctor_get(v_a_x3f_3795_, 0);
lean_inc(v_val_3797_);
lean_dec_ref(v_a_x3f_3795_);
v___x_3798_ = lean_apply_1(v_mkInfo_3793_, v_val_3797_);
v___x_3799_ = lean_apply_4(v_toBind_3790_, lean_box(0), lean_box(0), v___x_3798_, v___f_3794_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_3800_, lean_object* v_modifyInfoState_3801_, lean_object* v_toBind_3802_, lean_object* v_mkInfoOnError_3803_, lean_object* v_mkInfo_3804_, lean_object* v_inst_3805_, lean_object* v_x_3806_, lean_object* v___f_3807_, lean_object* v_treesSaved_3808_){
_start:
{
lean_object* v_toFunctor_3809_; lean_object* v_toPure_3810_; lean_object* v_map_3811_; lean_object* v___f_3812_; lean_object* v___f_3813_; lean_object* v___f_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_toFunctor_3809_ = lean_ctor_get(v_toApplicative_3800_, 0);
lean_inc_ref(v_toFunctor_3809_);
v_toPure_3810_ = lean_ctor_get(v_toApplicative_3800_, 1);
lean_inc(v_toPure_3810_);
lean_dec_ref(v_toApplicative_3800_);
v_map_3811_ = lean_ctor_get(v_toFunctor_3809_, 0);
lean_inc(v_map_3811_);
lean_dec_ref(v_toFunctor_3809_);
v___f_3812_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3812_, 0, v_treesSaved_3808_);
lean_closure_set(v___f_3812_, 1, v_modifyInfoState_3801_);
v___f_3813_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3813_, 0, v___f_3812_);
lean_inc_ref(v___f_3813_);
lean_inc(v_toBind_3802_);
v___f_3814_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3814_, 0, v_toPure_3810_);
lean_closure_set(v___f_3814_, 1, v_toBind_3802_);
lean_closure_set(v___f_3814_, 2, v___f_3813_);
v___f_3815_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_3815_, 0, v_toBind_3802_);
lean_closure_set(v___f_3815_, 1, v_mkInfoOnError_3803_);
lean_closure_set(v___f_3815_, 2, v___f_3814_);
lean_closure_set(v___f_3815_, 3, v_mkInfo_3804_);
lean_closure_set(v___f_3815_, 4, v___f_3813_);
v___x_3816_ = lean_apply_4(v_inst_3805_, lean_box(0), lean_box(0), v_x_3806_, v___f_3815_);
v___x_3817_ = lean_apply_4(v_map_3811_, lean_box(0), lean_box(0), v___f_3807_, v___x_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_3818_, lean_object* v_inst_3819_, lean_object* v_inst_3820_, lean_object* v_toBind_3821_, lean_object* v___f_3822_, lean_object* v_____do__lift_3823_){
_start:
{
uint8_t v_enabled_3824_; 
v_enabled_3824_ = lean_ctor_get_uint8(v_____do__lift_3823_, sizeof(void*)*3);
if (v_enabled_3824_ == 0)
{
lean_dec(v___f_3822_);
lean_dec(v_toBind_3821_);
lean_dec_ref(v_inst_3820_);
lean_dec_ref(v_inst_3819_);
lean_inc(v_x_3818_);
return v_x_3818_;
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3819_, v_inst_3820_);
v___x_3826_ = lean_apply_4(v_toBind_3821_, lean_box(0), lean_box(0), v___x_3825_, v___f_3822_);
return v___x_3826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_3827_, lean_object* v_inst_3828_, lean_object* v_inst_3829_, lean_object* v_toBind_3830_, lean_object* v___f_3831_, lean_object* v_____do__lift_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_3827_, v_inst_3828_, v_inst_3829_, v_toBind_3830_, v___f_3831_, v_____do__lift_3832_);
lean_dec_ref(v_____do__lift_3832_);
lean_dec(v_x_3827_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_3835_, lean_object* v_inst_3836_, lean_object* v_inst_3837_, lean_object* v_x_3838_, lean_object* v_mkInfo_3839_, lean_object* v_mkInfoOnError_3840_){
_start:
{
lean_object* v_toApplicative_3841_; lean_object* v_toBind_3842_; lean_object* v_getInfoState_3843_; lean_object* v_modifyInfoState_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; 
v_toApplicative_3841_ = lean_ctor_get(v_inst_3835_, 0);
v_toBind_3842_ = lean_ctor_get(v_inst_3835_, 1);
lean_inc(v_toBind_3842_);
v_getInfoState_3843_ = lean_ctor_get(v_inst_3836_, 0);
lean_inc(v_getInfoState_3843_);
v_modifyInfoState_3844_ = lean_ctor_get(v_inst_3836_, 1);
v___f_3845_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3838_);
lean_inc(v_toBind_3842_);
lean_inc(v_modifyInfoState_3844_);
lean_inc_ref(v_toApplicative_3841_);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_3846_, 0, v_toApplicative_3841_);
lean_closure_set(v___f_3846_, 1, v_modifyInfoState_3844_);
lean_closure_set(v___f_3846_, 2, v_toBind_3842_);
lean_closure_set(v___f_3846_, 3, v_mkInfoOnError_3840_);
lean_closure_set(v___f_3846_, 4, v_mkInfo_3839_);
lean_closure_set(v___f_3846_, 5, v_inst_3837_);
lean_closure_set(v___f_3846_, 6, v_x_3838_);
lean_closure_set(v___f_3846_, 7, v___f_3845_);
lean_inc(v_toBind_3842_);
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3847_, 0, v_x_3838_);
lean_closure_set(v___f_3847_, 1, v_inst_3835_);
lean_closure_set(v___f_3847_, 2, v_inst_3836_);
lean_closure_set(v___f_3847_, 3, v_toBind_3842_);
lean_closure_set(v___f_3847_, 4, v___f_3846_);
v___x_3848_ = lean_apply_4(v_toBind_3842_, lean_box(0), lean_box(0), v_getInfoState_3843_, v___f_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_00_u03b1_3852_, lean_object* v_inst_3853_, lean_object* v_x_3854_, lean_object* v_mkInfo_3855_, lean_object* v_mkInfoOnError_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3850_, v_inst_3851_, v_inst_3853_, v_x_3854_, v_mkInfo_3855_, v_mkInfoOnError_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3858_, lean_object* v_tree_3859_, lean_object* v_s_3860_){
_start:
{
uint8_t v_enabled_3861_; lean_object* v_assignment_3862_; lean_object* v_lazyAssignment_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3871_; 
v_enabled_3861_ = lean_ctor_get_uint8(v_s_3860_, sizeof(void*)*3);
v_assignment_3862_ = lean_ctor_get(v_s_3860_, 0);
v_lazyAssignment_3863_ = lean_ctor_get(v_s_3860_, 1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_s_3860_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v_s_3860_, 2);
lean_dec(v_unused_3872_);
v___x_3865_ = v_s_3860_;
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_lazyAssignment_3863_);
lean_inc(v_assignment_3862_);
lean_dec(v_s_3860_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3858_, v_tree_3859_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 2, v___x_3867_);
v___x_3869_ = v___x_3865_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_assignment_3862_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_lazyAssignment_3863_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v___x_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*3, v_enabled_3861_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3873_, lean_object* v_modifyInfoState_3874_, lean_object* v_tree_3875_){
_start:
{
lean_object* v___f_3876_; lean_object* v___x_3877_; 
v___f_3876_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3876_, 0, v_treesSaved_3873_);
lean_closure_set(v___f_3876_, 1, v_tree_3875_);
v___x_3877_ = lean_apply_1(v_modifyInfoState_3874_, v___f_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3878_, lean_object* v_toBind_3879_, lean_object* v___f_3880_, lean_object* v_st_3881_){
_start:
{
lean_object* v_trees_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_trees_3882_ = lean_ctor_get(v_st_3881_, 2);
lean_inc_ref(v_trees_3882_);
lean_dec_ref(v_st_3881_);
v___x_3883_ = lean_apply_1(v_mkInfoTree_3878_, v_trees_3882_);
v___x_3884_ = lean_apply_4(v_toBind_3879_, lean_box(0), lean_box(0), v___x_3883_, v___f_3880_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3885_, lean_object* v_getInfoState_3886_, lean_object* v___f_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_apply_4(v_toBind_3885_, lean_box(0), lean_box(0), v_getInfoState_3886_, v___f_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3890_, lean_object* v_getInfoState_3891_, lean_object* v___f_3892_, lean_object* v_x_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3890_, v_getInfoState_3891_, v___f_3892_, v_x_3893_);
lean_dec(v_x_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_3895_, lean_object* v_modifyInfoState_3896_, lean_object* v_mkInfoTree_3897_, lean_object* v_toBind_3898_, lean_object* v_getInfoState_3899_, lean_object* v_inst_3900_, lean_object* v_x_3901_, lean_object* v___f_3902_, lean_object* v_treesSaved_3903_){
_start:
{
lean_object* v_toFunctor_3904_; lean_object* v_map_3905_; lean_object* v___f_3906_; lean_object* v___f_3907_; lean_object* v___f_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_toFunctor_3904_ = lean_ctor_get(v_toApplicative_3895_, 0);
lean_inc_ref(v_toFunctor_3904_);
lean_dec_ref(v_toApplicative_3895_);
v_map_3905_ = lean_ctor_get(v_toFunctor_3904_, 0);
lean_inc(v_map_3905_);
lean_dec_ref(v_toFunctor_3904_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3906_, 0, v_treesSaved_3903_);
lean_closure_set(v___f_3906_, 1, v_modifyInfoState_3896_);
lean_inc(v_toBind_3898_);
v___f_3907_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3907_, 0, v_mkInfoTree_3897_);
lean_closure_set(v___f_3907_, 1, v_toBind_3898_);
lean_closure_set(v___f_3907_, 2, v___f_3906_);
v___f_3908_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3908_, 0, v_toBind_3898_);
lean_closure_set(v___f_3908_, 1, v_getInfoState_3899_);
lean_closure_set(v___f_3908_, 2, v___f_3907_);
v___x_3909_ = lean_apply_4(v_inst_3900_, lean_box(0), lean_box(0), v_x_3901_, v___f_3908_);
v___x_3910_ = lean_apply_4(v_map_3905_, lean_box(0), lean_box(0), v___f_3902_, v___x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3911_, lean_object* v_inst_3912_, lean_object* v_inst_3913_, lean_object* v_x_3914_, lean_object* v_mkInfoTree_3915_){
_start:
{
lean_object* v_toApplicative_3916_; lean_object* v_toBind_3917_; lean_object* v_getInfoState_3918_; lean_object* v_modifyInfoState_3919_; lean_object* v___f_3920_; lean_object* v___f_3921_; lean_object* v___f_3922_; lean_object* v___x_3923_; 
v_toApplicative_3916_ = lean_ctor_get(v_inst_3911_, 0);
v_toBind_3917_ = lean_ctor_get(v_inst_3911_, 1);
lean_inc(v_toBind_3917_);
v_getInfoState_3918_ = lean_ctor_get(v_inst_3912_, 0);
lean_inc(v_getInfoState_3918_);
v_modifyInfoState_3919_ = lean_ctor_get(v_inst_3912_, 1);
v___f_3920_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3914_);
lean_inc(v_getInfoState_3918_);
lean_inc(v_toBind_3917_);
lean_inc(v_modifyInfoState_3919_);
lean_inc_ref(v_toApplicative_3916_);
v___f_3921_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3921_, 0, v_toApplicative_3916_);
lean_closure_set(v___f_3921_, 1, v_modifyInfoState_3919_);
lean_closure_set(v___f_3921_, 2, v_mkInfoTree_3915_);
lean_closure_set(v___f_3921_, 3, v_toBind_3917_);
lean_closure_set(v___f_3921_, 4, v_getInfoState_3918_);
lean_closure_set(v___f_3921_, 5, v_inst_3913_);
lean_closure_set(v___f_3921_, 6, v_x_3914_);
lean_closure_set(v___f_3921_, 7, v___f_3920_);
lean_inc(v_toBind_3917_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3922_, 0, v_x_3914_);
lean_closure_set(v___f_3922_, 1, v_inst_3911_);
lean_closure_set(v___f_3922_, 2, v_inst_3912_);
lean_closure_set(v___f_3922_, 3, v_toBind_3917_);
lean_closure_set(v___f_3922_, 4, v___f_3921_);
v___x_3923_ = lean_apply_4(v_toBind_3917_, lean_box(0), lean_box(0), v_getInfoState_3918_, v___f_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3924_, lean_object* v_inst_3925_, lean_object* v_inst_3926_, lean_object* v_00_u03b1_3927_, lean_object* v_inst_3928_, lean_object* v_x_3929_, lean_object* v_mkInfoTree_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3925_, v_inst_3926_, v_inst_3928_, v_x_3929_, v_mkInfoTree_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3932_, lean_object* v_toPure_3933_, lean_object* v_____do__lift_3934_){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3935_, 0, v_____do__lift_3934_);
lean_ctor_set(v___x_3935_, 1, v_trees_3932_);
v___x_3936_ = lean_apply_2(v_toPure_3933_, lean_box(0), v___x_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3937_, lean_object* v_toBind_3938_, lean_object* v_mkInfo_3939_, lean_object* v_trees_3940_){
_start:
{
lean_object* v___f_3941_; lean_object* v___x_3942_; 
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3941_, 0, v_trees_3940_);
lean_closure_set(v___f_3941_, 1, v_toPure_3937_);
v___x_3942_ = lean_apply_4(v_toBind_3938_, lean_box(0), lean_box(0), v_mkInfo_3939_, v___f_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3943_, lean_object* v_inst_3944_, lean_object* v_inst_3945_, lean_object* v_x_3946_, lean_object* v_mkInfo_3947_){
_start:
{
lean_object* v_toApplicative_3948_; lean_object* v_toBind_3949_; lean_object* v_toPure_3950_; lean_object* v___f_3951_; lean_object* v___x_3952_; 
v_toApplicative_3948_ = lean_ctor_get(v_inst_3943_, 0);
v_toBind_3949_ = lean_ctor_get(v_inst_3943_, 1);
v_toPure_3950_ = lean_ctor_get(v_toApplicative_3948_, 1);
lean_inc(v_toBind_3949_);
lean_inc(v_toPure_3950_);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3951_, 0, v_toPure_3950_);
lean_closure_set(v___f_3951_, 1, v_toBind_3949_);
lean_closure_set(v___f_3951_, 2, v_mkInfo_3947_);
v___x_3952_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3943_, v_inst_3944_, v_inst_3945_, v_x_3946_, v___f_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3953_, lean_object* v_inst_3954_, lean_object* v_inst_3955_, lean_object* v_00_u03b1_3956_, lean_object* v_inst_3957_, lean_object* v_x_3958_, lean_object* v_mkInfo_3959_){
_start:
{
lean_object* v_toApplicative_3960_; lean_object* v_toBind_3961_; lean_object* v_toPure_3962_; lean_object* v___f_3963_; lean_object* v___x_3964_; 
v_toApplicative_3960_ = lean_ctor_get(v_inst_3954_, 0);
v_toBind_3961_ = lean_ctor_get(v_inst_3954_, 1);
v_toPure_3962_ = lean_ctor_get(v_toApplicative_3960_, 1);
lean_inc(v_toBind_3961_);
lean_inc(v_toPure_3962_);
v___f_3963_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3963_, 0, v_toPure_3962_);
lean_closure_set(v___f_3963_, 1, v_toBind_3961_);
lean_closure_set(v___f_3963_, 2, v_mkInfo_3959_);
v___x_3964_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3954_, v_inst_3955_, v_inst_3957_, v_x_3958_, v___f_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3965_, lean_object* v_trees_3966_, lean_object* v_s_3967_){
_start:
{
uint8_t v_enabled_3968_; lean_object* v_assignment_3969_; lean_object* v_lazyAssignment_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
v_enabled_3968_ = lean_ctor_get_uint8(v_s_3967_, sizeof(void*)*3);
v_assignment_3969_ = lean_ctor_get(v_s_3967_, 0);
v_lazyAssignment_3970_ = lean_ctor_get(v_s_3967_, 1);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_s_3967_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v_s_3967_, 2);
lean_dec(v_unused_3979_);
v___x_3972_ = v_s_3967_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_lazyAssignment_3970_);
lean_inc(v_assignment_3969_);
lean_dec(v_s_3967_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3965_, v_trees_3966_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 2, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_assignment_3969_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_lazyAssignment_3970_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v___x_3974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3977_, sizeof(void*)*3, v_enabled_3968_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3980_, lean_object* v_trees_3981_, lean_object* v_s_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3980_, v_trees_3981_, v_s_3982_);
lean_dec_ref(v_trees_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3984_, lean_object* v_modifyInfoState_3985_, lean_object* v_trees_3986_){
_start:
{
lean_object* v___f_3987_; lean_object* v___x_3988_; 
v___f_3987_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3987_, 0, v_treesSaved_3984_);
lean_closure_set(v___f_3987_, 1, v_trees_3986_);
v___x_3988_ = lean_apply_1(v_modifyInfoState_3985_, v___f_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3989_, lean_object* v_tree_3990_, lean_object* v_____do__lift_3991_){
_start:
{
if (lean_obj_tag(v_____do__lift_3991_) == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_apply_2(v_toPure_3989_, lean_box(0), v_tree_3990_);
return v___x_3992_;
}
else
{
lean_object* v_val_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v_val_3993_ = lean_ctor_get(v_____do__lift_3991_, 0);
lean_inc(v_val_3993_);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v_val_3993_);
lean_ctor_set(v___x_3994_, 1, v_tree_3990_);
v___x_3995_ = lean_apply_2(v_toPure_3989_, lean_box(0), v___x_3994_);
return v___x_3995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3996_, lean_object* v_tree_3997_, lean_object* v_____do__lift_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3996_, v_tree_3997_, v_____do__lift_3998_);
lean_dec(v_____do__lift_3998_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_4000_, lean_object* v_toPure_4001_, lean_object* v_toBind_4002_, lean_object* v_ctx_x3f_4003_, lean_object* v_tree_4004_){
_start:
{
lean_object* v_tree_4005_; lean_object* v___f_4006_; lean_object* v___x_4007_; 
v_tree_4005_ = l_Lean_Elab_InfoTree_substitute(v_tree_4004_, v_assignment_4000_);
v___f_4006_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4006_, 0, v_toPure_4001_);
lean_closure_set(v___f_4006_, 1, v_tree_4005_);
v___x_4007_ = lean_apply_4(v_toBind_4002_, lean_box(0), lean_box(0), v_ctx_x3f_4003_, v___f_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_4008_, lean_object* v_toBind_4009_, lean_object* v_ctx_x3f_4010_, lean_object* v_inst_4011_, lean_object* v___f_4012_, lean_object* v_st_4013_){
_start:
{
lean_object* v_assignment_4014_; lean_object* v_trees_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v_assignment_4014_ = lean_ctor_get(v_st_4013_, 0);
lean_inc_ref(v_assignment_4014_);
v_trees_4015_ = lean_ctor_get(v_st_4013_, 2);
lean_inc_ref(v_trees_4015_);
lean_dec_ref(v_st_4013_);
lean_inc(v_toBind_4009_);
v___f_4016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4016_, 0, v_assignment_4014_);
lean_closure_set(v___f_4016_, 1, v_toPure_4008_);
lean_closure_set(v___f_4016_, 2, v_toBind_4009_);
lean_closure_set(v___f_4016_, 3, v_ctx_x3f_4010_);
v___x_4017_ = l_Lean_PersistentArray_mapM___redArg(v_inst_4011_, v___f_4016_, v_trees_4015_);
v___x_4018_ = lean_apply_4(v_toBind_4009_, lean_box(0), lean_box(0), v___x_4017_, v___f_4012_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_4019_, lean_object* v_modifyInfoState_4020_, lean_object* v_toBind_4021_, lean_object* v_ctx_x3f_4022_, lean_object* v_inst_4023_, lean_object* v_getInfoState_4024_, lean_object* v_inst_4025_, lean_object* v_x_4026_, lean_object* v___f_4027_, lean_object* v_treesSaved_4028_){
_start:
{
lean_object* v_toFunctor_4029_; lean_object* v_toPure_4030_; lean_object* v_map_4031_; lean_object* v___f_4032_; lean_object* v___f_4033_; lean_object* v___f_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_toFunctor_4029_ = lean_ctor_get(v_toApplicative_4019_, 0);
lean_inc_ref(v_toFunctor_4029_);
v_toPure_4030_ = lean_ctor_get(v_toApplicative_4019_, 1);
lean_inc(v_toPure_4030_);
lean_dec_ref(v_toApplicative_4019_);
v_map_4031_ = lean_ctor_get(v_toFunctor_4029_, 0);
lean_inc(v_map_4031_);
lean_dec_ref(v_toFunctor_4029_);
v___f_4032_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4032_, 0, v_treesSaved_4028_);
lean_closure_set(v___f_4032_, 1, v_modifyInfoState_4020_);
lean_inc(v_toBind_4021_);
v___f_4033_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_4033_, 0, v_toPure_4030_);
lean_closure_set(v___f_4033_, 1, v_toBind_4021_);
lean_closure_set(v___f_4033_, 2, v_ctx_x3f_4022_);
lean_closure_set(v___f_4033_, 3, v_inst_4023_);
lean_closure_set(v___f_4033_, 4, v___f_4032_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_4034_, 0, v_toBind_4021_);
lean_closure_set(v___f_4034_, 1, v_getInfoState_4024_);
lean_closure_set(v___f_4034_, 2, v___f_4033_);
v___x_4035_ = lean_apply_4(v_inst_4025_, lean_box(0), lean_box(0), v_x_4026_, v___f_4034_);
v___x_4036_ = lean_apply_4(v_map_4031_, lean_box(0), lean_box(0), v___f_4027_, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_4037_, lean_object* v_inst_4038_, lean_object* v_inst_4039_, lean_object* v_x_4040_, lean_object* v_ctx_x3f_4041_){
_start:
{
lean_object* v_toApplicative_4042_; lean_object* v_toBind_4043_; lean_object* v_getInfoState_4044_; lean_object* v_modifyInfoState_4045_; lean_object* v___f_4046_; lean_object* v___f_4047_; lean_object* v___f_4048_; lean_object* v___x_4049_; 
v_toApplicative_4042_ = lean_ctor_get(v_inst_4037_, 0);
v_toBind_4043_ = lean_ctor_get(v_inst_4037_, 1);
lean_inc(v_toBind_4043_);
v_getInfoState_4044_ = lean_ctor_get(v_inst_4038_, 0);
lean_inc(v_getInfoState_4044_);
v_modifyInfoState_4045_ = lean_ctor_get(v_inst_4038_, 1);
v___f_4046_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4040_);
lean_inc(v_getInfoState_4044_);
lean_inc_ref(v_inst_4037_);
lean_inc(v_toBind_4043_);
lean_inc(v_modifyInfoState_4045_);
lean_inc_ref(v_toApplicative_4042_);
v___f_4047_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_4047_, 0, v_toApplicative_4042_);
lean_closure_set(v___f_4047_, 1, v_modifyInfoState_4045_);
lean_closure_set(v___f_4047_, 2, v_toBind_4043_);
lean_closure_set(v___f_4047_, 3, v_ctx_x3f_4041_);
lean_closure_set(v___f_4047_, 4, v_inst_4037_);
lean_closure_set(v___f_4047_, 5, v_getInfoState_4044_);
lean_closure_set(v___f_4047_, 6, v_inst_4039_);
lean_closure_set(v___f_4047_, 7, v_x_4040_);
lean_closure_set(v___f_4047_, 8, v___f_4046_);
lean_inc(v_toBind_4043_);
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4048_, 0, v_x_4040_);
lean_closure_set(v___f_4048_, 1, v_inst_4037_);
lean_closure_set(v___f_4048_, 2, v_inst_4038_);
lean_closure_set(v___f_4048_, 3, v_toBind_4043_);
lean_closure_set(v___f_4048_, 4, v___f_4047_);
v___x_4049_ = lean_apply_4(v_toBind_4043_, lean_box(0), lean_box(0), v_getInfoState_4044_, v___f_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_00_u03b1_4053_, lean_object* v_inst_4054_, lean_object* v_x_4055_, lean_object* v_ctx_x3f_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4051_, v_inst_4052_, v_inst_4054_, v_x_4055_, v_ctx_x3f_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_4058_, lean_object* v_____do__lift_4059_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_____do__lift_4059_);
v___x_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
v___x_4062_ = lean_apply_2(v_toPure_4058_, lean_box(0), v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_inst_4066_, lean_object* v_inst_4067_, lean_object* v_inst_4068_, lean_object* v_inst_4069_, lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_x_4072_){
_start:
{
lean_object* v_toApplicative_4073_; lean_object* v_toBind_4074_; lean_object* v_toPure_4075_; lean_object* v___x_4076_; lean_object* v___f_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_toApplicative_4073_ = lean_ctor_get(v_inst_4063_, 0);
v_toBind_4074_ = lean_ctor_get(v_inst_4063_, 1);
v_toPure_4075_ = lean_ctor_get(v_toApplicative_4073_, 1);
lean_inc_ref(v_inst_4063_);
v___x_4076_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_4063_, v_inst_4067_, v_inst_4069_, v_inst_4068_, v_inst_4070_, v_inst_4065_, v_inst_4071_);
lean_inc(v_toPure_4075_);
v___f_4077_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4077_, 0, v_toPure_4075_);
lean_inc(v_toBind_4074_);
v___x_4078_ = lean_apply_4(v_toBind_4074_, lean_box(0), lean_box(0), v___x_4076_, v___f_4077_);
v___x_4079_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4063_, v_inst_4064_, v_inst_4066_, v_x_4072_, v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_4080_, lean_object* v_inst_4081_, lean_object* v_inst_4082_, lean_object* v_00_u03b1_4083_, lean_object* v_inst_4084_, lean_object* v_inst_4085_, lean_object* v_inst_4086_, lean_object* v_inst_4087_, lean_object* v_inst_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_x_4091_){
_start:
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_4081_, v_inst_4082_, v_inst_4084_, v_inst_4085_, v_inst_4086_, v_inst_4087_, v_inst_4088_, v_inst_4089_, v_inst_4090_, v_x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_4093_, lean_object* v_____x_4094_){
_start:
{
if (lean_obj_tag(v_____x_4094_) == 1)
{
lean_object* v_val_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4104_; 
v_val_4095_ = lean_ctor_get(v_____x_4094_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_____x_4094_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4097_ = v_____x_4094_;
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_val_4095_);
lean_dec(v_____x_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_val_4095_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4099_);
v___x_4101_ = v___x_4097_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_apply_2(v_toPure_4093_, lean_box(0), v___x_4101_);
return v___x_4102_;
}
}
}
else
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_dec(v_____x_4094_);
v___x_4105_ = lean_box(0);
v___x_4106_ = lean_apply_2(v_toPure_4093_, lean_box(0), v___x_4105_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_4107_, lean_object* v_inst_4108_, lean_object* v_inst_4109_, lean_object* v_inst_4110_, lean_object* v_x_4111_){
_start:
{
lean_object* v_toApplicative_4112_; lean_object* v_toBind_4113_; lean_object* v_toPure_4114_; lean_object* v___f_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_toApplicative_4112_ = lean_ctor_get(v_inst_4107_, 0);
v_toBind_4113_ = lean_ctor_get(v_inst_4107_, 1);
v_toPure_4114_ = lean_ctor_get(v_toApplicative_4112_, 1);
lean_inc(v_toPure_4114_);
v___f_4115_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4115_, 0, v_toPure_4114_);
lean_inc(v_toBind_4113_);
v___x_4116_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v_inst_4110_, v___f_4115_);
v___x_4117_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4107_, v_inst_4108_, v_inst_4109_, v_x_4111_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_4118_, lean_object* v_inst_4119_, lean_object* v_inst_4120_, lean_object* v_00_u03b1_4121_, lean_object* v_inst_4122_, lean_object* v_inst_4123_, lean_object* v_x_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_4119_, v_inst_4120_, v_inst_4122_, v_inst_4123_, v_x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_4126_, lean_object* v_autoImplicits_4127_){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_autoImplicits_4127_);
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
v___x_4130_ = lean_apply_2(v_toPure_4126_, lean_box(0), v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_inst_4133_, lean_object* v_inst_4134_, lean_object* v_x_4135_){
_start:
{
lean_object* v_toApplicative_4136_; lean_object* v_toBind_4137_; lean_object* v_toPure_4138_; lean_object* v___f_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_toApplicative_4136_ = lean_ctor_get(v_inst_4131_, 0);
v_toBind_4137_ = lean_ctor_get(v_inst_4131_, 1);
v_toPure_4138_ = lean_ctor_get(v_toApplicative_4136_, 1);
lean_inc(v_toPure_4138_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4139_, 0, v_toPure_4138_);
lean_inc(v_toBind_4137_);
v___x_4140_ = lean_apply_4(v_toBind_4137_, lean_box(0), lean_box(0), v_inst_4134_, v___f_4139_);
v___x_4141_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_4131_, v_inst_4132_, v_inst_4133_, v_x_4135_, v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_4142_, lean_object* v_inst_4143_, lean_object* v_inst_4144_, lean_object* v_00_u03b1_4145_, lean_object* v_inst_4146_, lean_object* v_inst_4147_, lean_object* v_x_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_4143_, v_inst_4144_, v_inst_4146_, v_inst_4147_, v_x_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v_mvarId_4152_, lean_object* v_toPure_4153_, lean_object* v_____do__lift_4154_){
_start:
{
lean_object* v_assignment_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_assignment_4155_ = lean_ctor_get(v_____do__lift_4154_, 0);
lean_inc_ref(v_assignment_4155_);
lean_dec_ref(v_____do__lift_4154_);
v___x_4156_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_4150_, v___x_4151_, v_assignment_4155_, v_mvarId_4152_);
v___x_4157_ = lean_apply_2(v_toPure_4153_, lean_box(0), v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_4160_, lean_object* v_inst_4161_, lean_object* v_mvarId_4162_){
_start:
{
lean_object* v_toApplicative_4163_; lean_object* v_toBind_4164_; lean_object* v_getInfoState_4165_; lean_object* v_toPure_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___f_4169_; lean_object* v___x_4170_; 
v_toApplicative_4163_ = lean_ctor_get(v_inst_4160_, 0);
lean_inc_ref(v_toApplicative_4163_);
v_toBind_4164_ = lean_ctor_get(v_inst_4160_, 1);
lean_inc(v_toBind_4164_);
lean_dec_ref(v_inst_4160_);
v_getInfoState_4165_ = lean_ctor_get(v_inst_4161_, 0);
lean_inc(v_getInfoState_4165_);
lean_dec_ref(v_inst_4161_);
v_toPure_4166_ = lean_ctor_get(v_toApplicative_4163_, 1);
lean_inc(v_toPure_4166_);
lean_dec_ref(v_toApplicative_4163_);
v___x_4167_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4168_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_4169_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4169_, 0, v___x_4167_);
lean_closure_set(v___f_4169_, 1, v___x_4168_);
lean_closure_set(v___f_4169_, 2, v_mvarId_4162_);
lean_closure_set(v___f_4169_, 3, v_toPure_4166_);
v___x_4170_ = lean_apply_4(v_toBind_4164_, lean_box(0), lean_box(0), v_getInfoState_4165_, v___f_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_4171_, lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_mvarId_4174_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4172_, v_inst_4173_, v_mvarId_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_4176_, lean_object* v_infoTree_4177_, lean_object* v_s_4178_){
_start:
{
uint8_t v_enabled_4179_; lean_object* v_assignment_4180_; lean_object* v_lazyAssignment_4181_; lean_object* v_trees_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4192_; 
v_enabled_4179_ = lean_ctor_get_uint8(v_s_4178_, sizeof(void*)*3);
v_assignment_4180_ = lean_ctor_get(v_s_4178_, 0);
v_lazyAssignment_4181_ = lean_ctor_get(v_s_4178_, 1);
v_trees_4182_ = lean_ctor_get(v_s_4178_, 2);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_s_4178_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4184_ = v_s_4178_;
v_isShared_4185_ = v_isSharedCheck_4192_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_trees_4182_);
lean_inc(v_lazyAssignment_4181_);
lean_inc(v_assignment_4180_);
lean_dec(v_s_4178_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4192_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4186_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4187_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4188_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4186_, v___x_4187_, v_assignment_4180_, v_mvarId_4176_, v_infoTree_4177_);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v___x_4188_);
v___x_4190_ = v___x_4184_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v_lazyAssignment_4181_);
lean_ctor_set(v_reuseFailAlloc_4191_, 2, v_trees_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4191_, sizeof(void*)*3, v_enabled_4179_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4195_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_4196_ = lean_unsigned_to_nat(2u);
v___x_4197_ = lean_unsigned_to_nat(481u);
v___x_4198_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_4199_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1));
v___x_4200_ = l_mkPanicMessageWithDecl(v___x_4199_, v___x_4198_, v___x_4197_, v___x_4196_, v___x_4195_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_4201_, lean_object* v___f_4202_, lean_object* v_inst_4203_, lean_object* v_____do__lift_4204_){
_start:
{
if (lean_obj_tag(v_____do__lift_4204_) == 0)
{
lean_object* v_modifyInfoState_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_inst_4203_);
v_modifyInfoState_4205_ = lean_ctor_get(v_inst_4201_, 1);
lean_inc(v_modifyInfoState_4205_);
lean_dec_ref(v_inst_4201_);
v___x_4206_ = lean_apply_1(v_modifyInfoState_4205_, v___f_4202_);
return v___x_4206_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_dec_ref(v___f_4202_);
lean_dec_ref(v_inst_4201_);
v___x_4207_ = lean_box(0);
v___x_4208_ = l_instInhabitedOfMonad___redArg(v_inst_4203_, v___x_4207_);
v___x_4209_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2);
v___x_4210_ = l_panic___redArg(v___x_4208_, v___x_4209_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_4211_, lean_object* v___f_4212_, lean_object* v_inst_4213_, lean_object* v_____do__lift_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_4211_, v___f_4212_, v_inst_4213_, v_____do__lift_4214_);
lean_dec(v_____do__lift_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_4216_, lean_object* v_inst_4217_, lean_object* v_mvarId_4218_, lean_object* v_infoTree_4219_){
_start:
{
lean_object* v_toBind_4220_; lean_object* v___f_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v_toBind_4220_ = lean_ctor_get(v_inst_4216_, 1);
lean_inc(v_toBind_4220_);
lean_inc(v_mvarId_4218_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4221_, 0, v_mvarId_4218_);
lean_closure_set(v___f_4221_, 1, v_infoTree_4219_);
lean_inc_ref(v_inst_4216_);
lean_inc_ref(v_inst_4217_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4222_, 0, v_inst_4217_);
lean_closure_set(v___f_4222_, 1, v___f_4221_);
lean_closure_set(v___f_4222_, 2, v_inst_4216_);
v___x_4223_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_4216_, v_inst_4217_, v_mvarId_4218_);
v___x_4224_ = lean_apply_4(v_toBind_4220_, lean_box(0), lean_box(0), v___x_4223_, v___f_4222_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_4225_, lean_object* v_inst_4226_, lean_object* v_inst_4227_, lean_object* v_mvarId_4228_, lean_object* v_infoTree_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_4226_, v_inst_4227_, v_mvarId_4228_, v_infoTree_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_4231_, lean_object* v_output_4232_, lean_object* v_toPure_4233_, lean_object* v_____do__lift_4234_){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4235_, 0, v_____do__lift_4234_);
lean_ctor_set(v___x_4235_, 1, v_stx_4231_);
lean_ctor_set(v___x_4235_, 2, v_output_4232_);
v___x_4236_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
v___x_4237_ = lean_apply_2(v_toPure_4233_, lean_box(0), v___x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_4238_, lean_object* v_inst_4239_, lean_object* v_inst_4240_, lean_object* v_inst_4241_, lean_object* v_stx_4242_, lean_object* v_output_4243_, lean_object* v_x_4244_){
_start:
{
lean_object* v_toApplicative_4245_; lean_object* v_toBind_4246_; lean_object* v_toPure_4247_; lean_object* v___f_4248_; lean_object* v_mkInfo_4249_; lean_object* v___f_4250_; lean_object* v___x_4251_; 
v_toApplicative_4245_ = lean_ctor_get(v_inst_4239_, 0);
v_toBind_4246_ = lean_ctor_get(v_inst_4239_, 1);
v_toPure_4247_ = lean_ctor_get(v_toApplicative_4245_, 1);
lean_inc(v_toPure_4247_);
v___f_4248_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4248_, 0, v_stx_4242_);
lean_closure_set(v___f_4248_, 1, v_output_4243_);
lean_closure_set(v___f_4248_, 2, v_toPure_4247_);
lean_inc(v_toBind_4246_);
v_mkInfo_4249_ = lean_apply_4(v_toBind_4246_, lean_box(0), lean_box(0), v_inst_4241_, v___f_4248_);
lean_inc(v_toBind_4246_);
lean_inc(v_toPure_4247_);
v___f_4250_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4250_, 0, v_toPure_4247_);
lean_closure_set(v___f_4250_, 1, v_toBind_4246_);
lean_closure_set(v___f_4250_, 2, v_mkInfo_4249_);
v___x_4251_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_4239_, v_inst_4240_, v_inst_4238_, v_x_4244_, v___f_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_4252_, lean_object* v_00_u03b1_4253_, lean_object* v_inst_4254_, lean_object* v_inst_4255_, lean_object* v_inst_4256_, lean_object* v_inst_4257_, lean_object* v_stx_4258_, lean_object* v_output_4259_, lean_object* v_x_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_4254_, v_inst_4255_, v_inst_4256_, v_inst_4257_, v_stx_4258_, v_output_4259_, v_x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_4262_, lean_object* v_mvarId_4263_, lean_object* v_s_4264_){
_start:
{
lean_object* v_trees_4265_; uint8_t v_enabled_4266_; lean_object* v_assignment_4267_; lean_object* v_lazyAssignment_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4288_; 
v_trees_4265_ = lean_ctor_get(v_s_4264_, 2);
v_enabled_4266_ = lean_ctor_get_uint8(v_s_4264_, sizeof(void*)*3);
v_assignment_4267_ = lean_ctor_get(v_s_4264_, 0);
v_lazyAssignment_4268_ = lean_ctor_get(v_s_4264_, 1);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_s_4264_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4270_ = v_s_4264_;
v_isShared_4271_ = v_isSharedCheck_4288_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_trees_4265_);
lean_inc(v_lazyAssignment_4268_);
lean_inc(v_assignment_4267_);
lean_dec(v_s_4264_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4288_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v_size_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v_size_4272_ = lean_ctor_get(v_trees_4265_, 2);
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = lean_nat_dec_lt(v___x_4273_, v_size_4272_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4276_; 
lean_dec_ref(v_trees_4265_);
lean_dec(v_mvarId_4263_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 2, v_treesSaved_4262_);
v___x_4276_ = v___x_4270_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_assignment_4267_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_lazyAssignment_4268_);
lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_treesSaved_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, sizeof(void*)*3, v_enabled_4266_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4278_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_4279_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_4280_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = lean_nat_sub(v_size_4272_, v___x_4281_);
v___x_4283_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4280_, v_trees_4265_, v___x_4282_);
lean_dec(v___x_4282_);
v___x_4284_ = l_Lean_PersistentHashMap_insert___redArg(v___x_4278_, v___x_4279_, v_assignment_4267_, v_mvarId_4263_, v___x_4283_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 2, v_treesSaved_4262_);
lean_ctor_set(v___x_4270_, 0, v___x_4284_);
v___x_4286_ = v___x_4270_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_lazyAssignment_4268_);
lean_ctor_set(v_reuseFailAlloc_4287_, 2, v_treesSaved_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*3, v_enabled_4266_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_4289_, lean_object* v___f_4290_, lean_object* v_x_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_apply_1(v_modifyInfoState_4289_, v___f_4290_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_4293_, lean_object* v___f_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_4293_, v___f_4294_, v_x_4295_);
lean_dec(v_x_4295_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_4297_, lean_object* v_mvarId_4298_, lean_object* v_modifyInfoState_4299_, lean_object* v_inst_4300_, lean_object* v_x_4301_, lean_object* v___f_4302_, lean_object* v_treesSaved_4303_){
_start:
{
lean_object* v_toFunctor_4304_; lean_object* v_map_4305_; lean_object* v___f_4306_; lean_object* v___f_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_toFunctor_4304_ = lean_ctor_get(v_toApplicative_4297_, 0);
lean_inc_ref(v_toFunctor_4304_);
lean_dec_ref(v_toApplicative_4297_);
v_map_4305_ = lean_ctor_get(v_toFunctor_4304_, 0);
lean_inc(v_map_4305_);
lean_dec_ref(v_toFunctor_4304_);
v___f_4306_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4306_, 0, v_treesSaved_4303_);
lean_closure_set(v___f_4306_, 1, v_mvarId_4298_);
v___f_4307_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4307_, 0, v_modifyInfoState_4299_);
lean_closure_set(v___f_4307_, 1, v___f_4306_);
v___x_4308_ = lean_apply_4(v_inst_4300_, lean_box(0), lean_box(0), v_x_4301_, v___f_4307_);
v___x_4309_ = lean_apply_4(v_map_4305_, lean_box(0), lean_box(0), v___f_4302_, v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_mvarId_4313_, lean_object* v_x_4314_){
_start:
{
lean_object* v_toApplicative_4315_; lean_object* v_toBind_4316_; lean_object* v_getInfoState_4317_; lean_object* v_modifyInfoState_4318_; lean_object* v___f_4319_; lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; 
v_toApplicative_4315_ = lean_ctor_get(v_inst_4311_, 0);
v_toBind_4316_ = lean_ctor_get(v_inst_4311_, 1);
lean_inc(v_toBind_4316_);
v_getInfoState_4317_ = lean_ctor_get(v_inst_4312_, 0);
lean_inc(v_getInfoState_4317_);
v_modifyInfoState_4318_ = lean_ctor_get(v_inst_4312_, 1);
v___f_4319_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4314_);
lean_inc(v_modifyInfoState_4318_);
lean_inc_ref(v_toApplicative_4315_);
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4320_, 0, v_toApplicative_4315_);
lean_closure_set(v___f_4320_, 1, v_mvarId_4313_);
lean_closure_set(v___f_4320_, 2, v_modifyInfoState_4318_);
lean_closure_set(v___f_4320_, 3, v_inst_4310_);
lean_closure_set(v___f_4320_, 4, v_x_4314_);
lean_closure_set(v___f_4320_, 5, v___f_4319_);
lean_inc(v_toBind_4316_);
v___f_4321_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4321_, 0, v_x_4314_);
lean_closure_set(v___f_4321_, 1, v_inst_4311_);
lean_closure_set(v___f_4321_, 2, v_inst_4312_);
lean_closure_set(v___f_4321_, 3, v_toBind_4316_);
lean_closure_set(v___f_4321_, 4, v___f_4320_);
v___x_4322_ = lean_apply_4(v_toBind_4316_, lean_box(0), lean_box(0), v_getInfoState_4317_, v___f_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_4323_, lean_object* v_00_u03b1_4324_, lean_object* v_inst_4325_, lean_object* v_inst_4326_, lean_object* v_inst_4327_, lean_object* v_mvarId_4328_, lean_object* v_x_4329_){
_start:
{
lean_object* v_toApplicative_4330_; lean_object* v_toBind_4331_; lean_object* v_getInfoState_4332_; lean_object* v_modifyInfoState_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___f_4336_; lean_object* v___x_4337_; 
v_toApplicative_4330_ = lean_ctor_get(v_inst_4326_, 0);
v_toBind_4331_ = lean_ctor_get(v_inst_4326_, 1);
lean_inc(v_toBind_4331_);
v_getInfoState_4332_ = lean_ctor_get(v_inst_4327_, 0);
lean_inc(v_getInfoState_4332_);
v_modifyInfoState_4333_ = lean_ctor_get(v_inst_4327_, 1);
v___f_4334_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_4329_);
lean_inc(v_modifyInfoState_4333_);
lean_inc_ref(v_toApplicative_4330_);
v___f_4335_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4335_, 0, v_toApplicative_4330_);
lean_closure_set(v___f_4335_, 1, v_mvarId_4328_);
lean_closure_set(v___f_4335_, 2, v_modifyInfoState_4333_);
lean_closure_set(v___f_4335_, 3, v_inst_4325_);
lean_closure_set(v___f_4335_, 4, v_x_4329_);
lean_closure_set(v___f_4335_, 5, v___f_4334_);
lean_inc(v_toBind_4331_);
v___f_4336_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4336_, 0, v_x_4329_);
lean_closure_set(v___f_4336_, 1, v_inst_4326_);
lean_closure_set(v___f_4336_, 2, v_inst_4327_);
lean_closure_set(v___f_4336_, 3, v_toBind_4331_);
lean_closure_set(v___f_4336_, 4, v___f_4335_);
v___x_4337_ = lean_apply_4(v_toBind_4331_, lean_box(0), lean_box(0), v_getInfoState_4332_, v___f_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_4338_, lean_object* v_s_4339_){
_start:
{
lean_object* v_assignment_4340_; lean_object* v_lazyAssignment_4341_; lean_object* v_trees_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_assignment_4340_ = lean_ctor_get(v_s_4339_, 0);
v_lazyAssignment_4341_ = lean_ctor_get(v_s_4339_, 1);
v_trees_4342_ = lean_ctor_get(v_s_4339_, 2);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_s_4339_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v_s_4339_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_trees_4342_);
lean_inc(v_lazyAssignment_4341_);
lean_inc(v_assignment_4340_);
lean_dec(v_s_4339_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_assignment_4340_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_lazyAssignment_4341_);
lean_ctor_set(v_reuseFailAlloc_4348_, 2, v_trees_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_ctor_set_uint8(v___x_4347_, sizeof(void*)*3, v_flag_4338_);
return v___x_4347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_4350_, lean_object* v_s_4351_){
_start:
{
uint8_t v_flag_boxed_4352_; lean_object* v_res_4353_; 
v_flag_boxed_4352_ = lean_unbox(v_flag_4350_);
v_res_4353_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_4352_, v_s_4351_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_4354_, uint8_t v_flag_4355_){
_start:
{
lean_object* v_modifyInfoState_4356_; lean_object* v___x_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; 
v_modifyInfoState_4356_ = lean_ctor_get(v_inst_4354_, 1);
lean_inc(v_modifyInfoState_4356_);
lean_dec_ref(v_inst_4354_);
v___x_4357_ = lean_box(v_flag_4355_);
v___f_4358_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4358_, 0, v___x_4357_);
v___x_4359_ = lean_apply_1(v_modifyInfoState_4356_, v___f_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_4360_, lean_object* v_flag_4361_){
_start:
{
uint8_t v_flag_boxed_4362_; lean_object* v_res_4363_; 
v_flag_boxed_4362_ = lean_unbox(v_flag_4361_);
v_res_4363_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4360_, v_flag_boxed_4362_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_4364_, lean_object* v_inst_4365_, uint8_t v_flag_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4365_, v_flag_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_4368_, lean_object* v_inst_4369_, lean_object* v_flag_4370_){
_start:
{
uint8_t v_flag_boxed_4371_; lean_object* v_res_4372_; 
v_flag_boxed_4371_ = lean_unbox(v_flag_4370_);
v_res_4372_ = l_Lean_Elab_enableInfoTree(v_m_4368_, v_inst_4369_, v_flag_boxed_4371_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_4373_){
_start:
{
lean_object* v_fst_4374_; 
v_fst_4374_ = lean_ctor_get(v_x_4373_, 0);
lean_inc(v_fst_4374_);
return v_fst_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_4375_);
lean_dec_ref(v_x_4375_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_4377_, lean_object* v_____r_4378_){
_start:
{
lean_inc(v_x_4377_);
return v_x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_4379_, lean_object* v_____r_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_4379_, v_____r_4380_);
lean_dec(v_x_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_4382_, lean_object* v_x_4383_){
_start:
{
lean_inc(v___x_4382_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_4384_, lean_object* v_x_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_4384_, v_x_4385_);
lean_dec(v_x_4385_);
lean_dec(v___x_4384_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_4387_, lean_object* v_inst_4388_, uint8_t v_flag_4389_, lean_object* v_toBind_4390_, lean_object* v___f_4391_, lean_object* v_inst_4392_, lean_object* v___f_4393_, lean_object* v_____do__lift_4394_){
_start:
{
uint8_t v_enabled_4395_; lean_object* v_map_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; lean_object* v_y_4401_; lean_object* v___x_4402_; 
v_enabled_4395_ = lean_ctor_get_uint8(v_____do__lift_4394_, sizeof(void*)*3);
v_map_4396_ = lean_ctor_get(v_toFunctor_4387_, 0);
lean_inc(v_map_4396_);
lean_dec_ref(v_toFunctor_4387_);
lean_inc_ref(v_inst_4388_);
v___x_4397_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4388_, v_flag_4389_);
v___x_4398_ = lean_apply_4(v_toBind_4390_, lean_box(0), lean_box(0), v___x_4397_, v___f_4391_);
v___x_4399_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_4388_, v_enabled_4395_);
v___f_4400_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4400_, 0, v___x_4399_);
v_y_4401_ = lean_apply_4(v_inst_4392_, lean_box(0), lean_box(0), v___x_4398_, v___f_4400_);
v___x_4402_ = lean_apply_4(v_map_4396_, lean_box(0), lean_box(0), v___f_4393_, v_y_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_4403_, lean_object* v_inst_4404_, lean_object* v_flag_4405_, lean_object* v_toBind_4406_, lean_object* v___f_4407_, lean_object* v_inst_4408_, lean_object* v___f_4409_, lean_object* v_____do__lift_4410_){
_start:
{
uint8_t v_flag_boxed_4411_; lean_object* v_res_4412_; 
v_flag_boxed_4411_ = lean_unbox(v_flag_4405_);
v_res_4412_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_4403_, v_inst_4404_, v_flag_boxed_4411_, v_toBind_4406_, v___f_4407_, v_inst_4408_, v___f_4409_, v_____do__lift_4410_);
lean_dec_ref(v_____do__lift_4410_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_4414_, lean_object* v_inst_4415_, lean_object* v_inst_4416_, uint8_t v_flag_4417_, lean_object* v_x_4418_){
_start:
{
lean_object* v_toApplicative_4419_; lean_object* v_toBind_4420_; lean_object* v_getInfoState_4421_; lean_object* v_toFunctor_4422_; lean_object* v___f_4423_; lean_object* v___f_4424_; lean_object* v___x_4425_; lean_object* v___f_4426_; lean_object* v___x_4427_; 
v_toApplicative_4419_ = lean_ctor_get(v_inst_4414_, 0);
lean_inc_ref(v_toApplicative_4419_);
v_toBind_4420_ = lean_ctor_get(v_inst_4414_, 1);
lean_inc(v_toBind_4420_);
lean_dec_ref(v_inst_4414_);
v_getInfoState_4421_ = lean_ctor_get(v_inst_4415_, 0);
lean_inc(v_getInfoState_4421_);
v_toFunctor_4422_ = lean_ctor_get(v_toApplicative_4419_, 0);
lean_inc_ref(v_toFunctor_4422_);
lean_dec_ref(v_toApplicative_4419_);
v___f_4423_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_4424_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4424_, 0, v_x_4418_);
v___x_4425_ = lean_box(v_flag_4417_);
lean_inc(v_toBind_4420_);
v___f_4426_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_4426_, 0, v_toFunctor_4422_);
lean_closure_set(v___f_4426_, 1, v_inst_4415_);
lean_closure_set(v___f_4426_, 2, v___x_4425_);
lean_closure_set(v___f_4426_, 3, v_toBind_4420_);
lean_closure_set(v___f_4426_, 4, v___f_4424_);
lean_closure_set(v___f_4426_, 5, v_inst_4416_);
lean_closure_set(v___f_4426_, 6, v___f_4423_);
v___x_4427_ = lean_apply_4(v_toBind_4420_, lean_box(0), lean_box(0), v_getInfoState_4421_, v___f_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_4428_, lean_object* v_inst_4429_, lean_object* v_inst_4430_, lean_object* v_flag_4431_, lean_object* v_x_4432_){
_start:
{
uint8_t v_flag_boxed_4433_; lean_object* v_res_4434_; 
v_flag_boxed_4433_ = lean_unbox(v_flag_4431_);
v_res_4434_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4428_, v_inst_4429_, v_inst_4430_, v_flag_boxed_4433_, v_x_4432_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_4435_, lean_object* v_00_u03b1_4436_, lean_object* v_inst_4437_, lean_object* v_inst_4438_, lean_object* v_inst_4439_, uint8_t v_flag_4440_, lean_object* v_x_4441_){
_start:
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_4437_, v_inst_4438_, v_inst_4439_, v_flag_4440_, v_x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_4443_, lean_object* v_00_u03b1_4444_, lean_object* v_inst_4445_, lean_object* v_inst_4446_, lean_object* v_inst_4447_, lean_object* v_flag_4448_, lean_object* v_x_4449_){
_start:
{
uint8_t v_flag_boxed_4450_; lean_object* v_res_4451_; 
v_flag_boxed_4450_ = lean_unbox(v_flag_4448_);
v_res_4451_ = l_Lean_Elab_withEnableInfoTree(v_m_4443_, v_00_u03b1_4444_, v_inst_4445_, v_inst_4446_, v_inst_4447_, v_flag_boxed_4450_, v_x_4449_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_4452_, lean_object* v_____do__lift_4453_){
_start:
{
lean_object* v_trees_4454_; lean_object* v___x_4455_; 
v_trees_4454_ = lean_ctor_get(v_____do__lift_4453_, 2);
lean_inc_ref(v_trees_4454_);
lean_dec_ref(v_____do__lift_4453_);
v___x_4455_ = lean_apply_2(v_toPure_4452_, lean_box(0), v_trees_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_4456_, lean_object* v_inst_4457_){
_start:
{
lean_object* v_toApplicative_4458_; lean_object* v_toBind_4459_; lean_object* v_getInfoState_4460_; lean_object* v_toPure_4461_; lean_object* v___f_4462_; lean_object* v___x_4463_; 
v_toApplicative_4458_ = lean_ctor_get(v_inst_4457_, 0);
lean_inc_ref(v_toApplicative_4458_);
v_toBind_4459_ = lean_ctor_get(v_inst_4457_, 1);
lean_inc(v_toBind_4459_);
lean_dec_ref(v_inst_4457_);
v_getInfoState_4460_ = lean_ctor_get(v_inst_4456_, 0);
lean_inc(v_getInfoState_4460_);
lean_dec_ref(v_inst_4456_);
v_toPure_4461_ = lean_ctor_get(v_toApplicative_4458_, 1);
lean_inc(v_toPure_4461_);
lean_dec_ref(v_toApplicative_4458_);
v___f_4462_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4462_, 0, v_toPure_4461_);
v___x_4463_ = lean_apply_4(v_toBind_4459_, lean_box(0), lean_box(0), v_getInfoState_4460_, v___f_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_4464_, lean_object* v_inst_4465_, lean_object* v_inst_4466_){
_start:
{
lean_object* v___x_4467_; 
v___x_4467_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_4465_, v_inst_4466_);
return v___x_4467_;
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
