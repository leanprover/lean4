// Lean compiler output
// Module: Lean.Elab.InfoTree.Main
// Imports: public import Lean.Elab.InfoTree.Basic public import Lean.Meta.PPGoal public import Lean.ReservedNameAction import Init.Data.Format.Macro
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_CompletionInfo_stx(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3;
static const lean_ctor_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10;
static const lean_array_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0(lean_object*);
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
static const lean_string_object l_Lean_Elab_ContextInfo_ppGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no goals"};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__4 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ContextInfo_ppGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__4_value)}};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__5 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__5_value;
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
static const lean_string_object l_Lean_Elab_UserWidgetInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[UserWidget] "};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_UserWidgetInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__3_value;
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
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "[ChoiceResolution] alternative "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__5_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ") @ "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__6 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__7 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[Doc] "};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocElabInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "[DocElab] "};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocElabInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Main"};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.assignInfoHoleId"};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "assertion violation: ( __do_lift._@.Lean.Elab.InfoTree.Main.2379084842._hygCtx._hyg.19.0 ).isNone\n  "};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_____do__lift_47_, lean_object* v_toPure_48_, lean_object* v_toBind_49_, lean_object* v_____do__lift_50_){
_start:
{
lean_object* v_getOptions_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v_getOptions_51_ = lean_ctor_get(v_inst_44_, 0);
lean_inc(v_getOptions_51_);
lean_dec_ref(v_inst_44_);
lean_inc(v_toBind_49_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3), 7, 6);
lean_closure_set(v___f_52_, 0, v_inst_45_);
lean_closure_set(v___f_52_, 1, v_inst_46_);
lean_closure_set(v___f_52_, 2, v_____do__lift_47_);
lean_closure_set(v___f_52_, 3, v_____do__lift_50_);
lean_closure_set(v___f_52_, 4, v_toPure_48_);
lean_closure_set(v___f_52_, 5, v_toBind_49_);
v___x_53_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v_getOptions_51_, v___f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_toPure_58_, lean_object* v_toBind_59_, lean_object* v_____do__lift_60_){
_start:
{
lean_object* v_getMCtx_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v_getMCtx_61_ = lean_ctor_get(v_inst_54_, 0);
lean_inc(v_getMCtx_61_);
lean_dec_ref(v_inst_54_);
lean_inc(v_toBind_59_);
v___f_62_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4), 7, 6);
lean_closure_set(v___f_62_, 0, v_inst_55_);
lean_closure_set(v___f_62_, 1, v_inst_56_);
lean_closure_set(v___f_62_, 2, v_inst_57_);
lean_closure_set(v___f_62_, 3, v_____do__lift_60_);
lean_closure_set(v___f_62_, 4, v_toPure_58_);
lean_closure_set(v___f_62_, 5, v_toBind_59_);
v___x_63_ = lean_apply_4(v_toBind_59_, lean_box(0), lean_box(0), v_getMCtx_61_, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_toApplicative_70_; lean_object* v_toBind_71_; lean_object* v_getEnv_72_; lean_object* v_toPure_73_; lean_object* v___f_74_; lean_object* v___x_75_; 
v_toApplicative_70_ = lean_ctor_get(v_inst_64_, 0);
lean_inc_ref(v_toApplicative_70_);
v_toBind_71_ = lean_ctor_get(v_inst_64_, 1);
lean_inc_n(v_toBind_71_, 2);
lean_dec_ref(v_inst_64_);
v_getEnv_72_ = lean_ctor_get(v_inst_65_, 0);
lean_inc(v_getEnv_72_);
lean_dec_ref(v_inst_65_);
v_toPure_73_ = lean_ctor_get(v_toApplicative_70_, 1);
lean_inc(v_toPure_73_);
lean_dec_ref(v_toApplicative_70_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5), 7, 6);
lean_closure_set(v___f_74_, 0, v_inst_66_);
lean_closure_set(v___f_74_, 1, v_inst_67_);
lean_closure_set(v___f_74_, 2, v_inst_68_);
lean_closure_set(v___f_74_, 3, v_inst_69_);
lean_closure_set(v___f_74_, 4, v_toPure_73_);
lean_closure_set(v___f_74_, 5, v_toBind_71_);
v___x_75_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v_getEnv_72_, v___f_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap(lean_object* v_m_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_inst_81_, v_inst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(lean_object* v_ctx_84_, lean_object* v_toPure_85_, lean_object* v_____do__lift_86_){
_start:
{
lean_object* v_env_87_; lean_object* v_cmdEnv_x3f_88_; lean_object* v_mctx_89_; lean_object* v_options_90_; lean_object* v_currNamespace_91_; lean_object* v_openDecls_92_; lean_object* v_ngen_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_env_87_ = lean_ctor_get(v_ctx_84_, 0);
v_cmdEnv_x3f_88_ = lean_ctor_get(v_ctx_84_, 1);
v_mctx_89_ = lean_ctor_get(v_ctx_84_, 3);
v_options_90_ = lean_ctor_get(v_ctx_84_, 4);
v_currNamespace_91_ = lean_ctor_get(v_ctx_84_, 5);
v_openDecls_92_ = lean_ctor_get(v_ctx_84_, 6);
v_ngen_93_ = lean_ctor_get(v_ctx_84_, 7);
v_isSharedCheck_101_ = !lean_is_exclusive(v_ctx_84_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_ctx_84_, 2);
lean_dec(v_unused_102_);
v___x_95_ = v_ctx_84_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_ngen_93_);
lean_inc(v_openDecls_92_);
lean_inc(v_currNamespace_91_);
lean_inc(v_options_90_);
lean_inc(v_mctx_89_);
lean_inc(v_cmdEnv_x3f_88_);
lean_inc(v_env_87_);
lean_dec(v_ctx_84_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 2, v_____do__lift_86_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_env_87_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_cmdEnv_x3f_88_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_____do__lift_86_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_mctx_89_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v_options_90_);
lean_ctor_set(v_reuseFailAlloc_100_, 5, v_currNamespace_91_);
lean_ctor_set(v_reuseFailAlloc_100_, 6, v_openDecls_92_);
lean_ctor_set(v_reuseFailAlloc_100_, 7, v_ngen_93_);
v___x_98_ = v_reuseFailAlloc_100_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_2(v_toPure_85_, lean_box(0), v___x_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(lean_object* v_toPure_103_, lean_object* v_toBind_104_, lean_object* v_inst_105_, lean_object* v_ctx_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_107_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__0), 3, 2);
lean_closure_set(v___f_107_, 0, v_ctx_106_);
lean_closure_set(v___f_107_, 1, v_toPure_103_);
v___x_108_ = lean_apply_4(v_toBind_104_, lean_box(0), lean_box(0), v_inst_105_, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg(lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v_toApplicative_116_; lean_object* v_toBind_117_; lean_object* v_toPure_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_toApplicative_116_ = lean_ctor_get(v_inst_109_, 0);
v_toBind_117_ = lean_ctor_get(v_inst_109_, 1);
lean_inc_n(v_toBind_117_, 2);
v_toPure_118_ = lean_ctor_get(v_toApplicative_116_, 1);
lean_inc(v_toPure_118_);
v___x_119_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_inst_114_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__1), 4, 3);
lean_closure_set(v___f_120_, 0, v_toPure_118_);
lean_closure_set(v___f_120_, 1, v_toBind_117_);
lean_closure_set(v___f_120_, 2, v_inst_115_);
v___x_121_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_119_, v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save(lean_object* v_m_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_123_, v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object* v_x_137_){
_start:
{
lean_object* v_value_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_152_; 
v_value_138_ = lean_ctor_get(v_x_137_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v_x_137_, 0);
lean_dec(v_unused_153_);
v___x_140_ = v_x_137_;
v_isShared_141_ = v_isSharedCheck_152_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_value_138_);
lean_dec(v_x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_152_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_142_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__1));
v___x_143_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_138_);
lean_dec(v_value_138_);
v___x_144_ = 1;
v___x_145_ = l_Lean_Name_toString(v___x_143_, v___x_144_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 5);
lean_ctor_set(v___x_140_, 1, v___x_146_);
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_148_ = v___x_140_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_151_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__3));
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_156_, lean_object* v_opt_157_){
_start:
{
lean_object* v_name_158_; lean_object* v_defValue_159_; lean_object* v_map_160_; lean_object* v___x_161_; 
v_name_158_ = lean_ctor_get(v_opt_157_, 0);
v_defValue_159_ = lean_ctor_get(v_opt_157_, 1);
v_map_160_ = lean_ctor_get(v_opts_156_, 0);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_160_, v_name_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_inc(v_defValue_159_);
return v_defValue_159_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_161_, 1);
if (lean_obj_tag(v_val_162_) == 3)
{
lean_object* v_v_163_; 
v_v_163_ = lean_ctor_get(v_val_162_, 0);
lean_inc(v_v_163_);
lean_dec_ref_known(v_val_162_, 1);
return v_v_163_;
}
else
{
lean_dec(v_val_162_);
lean_inc(v_defValue_159_);
return v_defValue_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_164_, lean_object* v_opt_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_164_, v_opt_165_);
lean_dec_ref(v_opt_165_);
lean_dec_ref(v_opts_164_);
return v_res_166_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = l_Lean_Options_empty;
v___x_169_ = l_Lean_Core_getMaxHeartbeats(v___x_168_);
return v___x_169_;
}
}
static uint16_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_170_; uint16_t v___x_171_; 
v___x_170_ = l_Lean_Options_empty;
v___x_171_ = l_Lean_OptionFlags_ofOptions(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = l_Lean_firstFrontendMacroScope;
v___x_174_ = lean_nat_add(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
size_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_unsigned_to_nat(32u);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
lean_ctor_set(v___x_187_, 2, v___x_183_);
lean_ctor_set(v___x_187_, 3, v___x_183_);
lean_ctor_set_usize(v___x_187_, 4, v___x_182_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7(void){
_start:
{
lean_object* v___x_188_; uint64_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_189_ = 0ULL;
v___x_190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint64(v___x_190_, sizeof(void*)*1, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Lean_Options_empty;
v___x_200_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_201_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v___x_198_);
lean_ctor_set(v___x_201_, 4, v___x_198_);
lean_ctor_set(v___x_201_, 5, v___x_198_);
lean_ctor_set(v___x_201_, 6, v___x_200_);
lean_ctor_set(v___x_201_, 7, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = l_Lean_NameSet_empty;
v___x_203_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
lean_ctor_set(v___x_204_, 2, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_206_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_207_ = 1;
v___x_208_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_205_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*3, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = l_Lean_maxRecDepth;
v___x_213_ = l_Lean_Options_empty;
v___x_214_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static uint16_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19(void){
_start:
{
uint16_t v___x_215_; uint16_t v___x_216_; uint16_t v___x_217_; 
v___x_215_ = 512;
v___x_216_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_217_ = lean_uint16_land(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20(void){
_start:
{
uint16_t v___x_218_; uint16_t v___x_219_; uint8_t v___x_220_; 
v___x_218_ = 0;
v___x_219_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19);
v___x_220_ = lean_uint16_dec_eq(v___x_219_, v___x_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_a_225_; lean_object* v_toCommandContextInfo_228_; lean_object* v_env_229_; lean_object* v_options_230_; lean_object* v_currNamespace_231_; lean_object* v_openDecls_232_; lean_object* v_ngen_233_; uint8_t v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint16_t v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___y_260_; lean_object* v___y_261_; uint16_t v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; uint8_t v___y_335_; uint16_t v___y_336_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v_fileName_371_; lean_object* v_fileMap_372_; lean_object* v_currNamespace_373_; lean_object* v_openDecls_374_; lean_object* v_initHeartbeats_375_; lean_object* v_maxHeartbeats_376_; lean_object* v_quotContext_377_; lean_object* v_currMacroScope_378_; lean_object* v_cancelTk_x3f_379_; lean_object* v_inheritedTraceOptions_380_; lean_object* v_currRecDepth_381_; lean_object* v_ref_382_; uint8_t v_suppressElabErrors_383_; uint8_t v_checkDeprecated_384_; uint8_t v_isRecordingDeps_385_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___y_394_; lean_object* v_env_415_; uint8_t v___x_416_; uint8_t v___x_417_; 
v_toCommandContextInfo_228_ = lean_ctor_get(v_info_221_, 0);
lean_inc_ref(v_toCommandContextInfo_228_);
lean_dec_ref(v_info_221_);
v_env_229_ = lean_ctor_get(v_toCommandContextInfo_228_, 0);
lean_inc_ref(v_env_229_);
v_options_230_ = lean_ctor_get(v_toCommandContextInfo_228_, 4);
lean_inc_ref(v_options_230_);
v_currNamespace_231_ = lean_ctor_get(v_toCommandContextInfo_228_, 5);
lean_inc(v_currNamespace_231_);
v_openDecls_232_ = lean_ctor_get(v_toCommandContextInfo_228_, 6);
lean_inc(v_openDecls_232_);
v_ngen_233_ = lean_ctor_get(v_toCommandContextInfo_228_, 7);
lean_inc_ref(v_ngen_233_);
lean_dec_ref(v_toCommandContextInfo_228_);
v___x_234_ = 0;
v_env_235_ = l_Lean_Environment_setExporting(v_env_229_, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0));
v___x_237_ = l_Lean_instInhabitedFileMap_default;
v___x_238_ = l_Lean_Options_empty;
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_firstFrontendMacroScope;
v___x_243_ = lean_box(0);
v___x_244_ = lean_box(0);
v___x_245_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_246_ = 0;
v___x_247_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_248_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4));
v___x_249_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_250_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10);
v___x_251_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_252_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12);
v___x_253_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_254_ = 1;
v___x_255_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_256_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_256_, 0, v_env_235_);
lean_ctor_set(v___x_256_, 1, v___x_247_);
lean_ctor_set(v___x_256_, 2, v_ngen_233_);
lean_ctor_set(v___x_256_, 3, v___x_248_);
lean_ctor_set(v___x_256_, 4, v___x_249_);
lean_ctor_set(v___x_256_, 5, v___x_250_);
lean_ctor_set(v___x_256_, 6, v___x_252_);
lean_ctor_set(v___x_256_, 7, v___x_253_);
lean_ctor_set(v___x_256_, 8, v___x_255_);
lean_ctor_set(v___x_256_, 9, v___x_251_);
v___x_257_ = lean_io_get_num_heartbeats();
v___x_258_ = lean_st_mk_ref(v___x_256_);
v___x_390_ = l_Lean_inheritedTraceOptions;
v___x_391_ = lean_st_ref_get(v___x_390_);
v___x_392_ = lean_st_ref_get(v___x_258_);
v_env_415_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_415_);
lean_dec(v___x_392_);
v___x_416_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_415_);
lean_dec_ref(v_env_415_);
v___x_417_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20);
if (v___x_417_ == 0)
{
if (v___x_416_ == 0)
{
v___y_394_ = v___x_254_;
goto v___jp_393_;
}
else
{
v_fileName_371_ = v___x_236_;
v_fileMap_372_ = v___x_237_;
v_currNamespace_373_ = v_currNamespace_231_;
v_openDecls_374_ = v_openDecls_232_;
v_initHeartbeats_375_ = v___x_257_;
v_maxHeartbeats_376_ = v___x_240_;
v_quotContext_377_ = v___x_241_;
v_currMacroScope_378_ = v___x_242_;
v_cancelTk_x3f_379_ = v___x_243_;
v_inheritedTraceOptions_380_ = v___x_391_;
v_currRecDepth_381_ = v___x_239_;
v_ref_382_ = v___x_244_;
v_suppressElabErrors_383_ = v___x_234_;
v_checkDeprecated_384_ = v___x_246_;
v_isRecordingDeps_385_ = v___x_234_;
goto v___jp_370_;
}
}
else
{
if (v___x_416_ == 0)
{
v_fileName_371_ = v___x_236_;
v_fileMap_372_ = v___x_237_;
v_currNamespace_373_ = v_currNamespace_231_;
v_openDecls_374_ = v_openDecls_232_;
v_initHeartbeats_375_ = v___x_257_;
v_maxHeartbeats_376_ = v___x_240_;
v_quotContext_377_ = v___x_241_;
v_currMacroScope_378_ = v___x_242_;
v_cancelTk_x3f_379_ = v___x_243_;
v_inheritedTraceOptions_380_ = v___x_391_;
v_currRecDepth_381_ = v___x_239_;
v_ref_382_ = v___x_244_;
v_suppressElabErrors_383_ = v___x_234_;
v_checkDeprecated_384_ = v___x_246_;
v_isRecordingDeps_385_ = v___x_234_;
goto v___jp_370_;
}
else
{
v___y_394_ = v___x_234_;
goto v___jp_393_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_mk_io_user_error(v_a_225_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
v___jp_259_:
{
lean_object* v_toCold_265_; lean_object* v_currRecDepth_266_; lean_object* v_ref_267_; uint8_t v_suppressElabErrors_268_; uint8_t v_checkDeprecated_269_; uint8_t v_isRecordingDeps_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_329_; 
v_toCold_265_ = lean_ctor_get(v___y_263_, 0);
v_currRecDepth_266_ = lean_ctor_get(v___y_263_, 1);
v_ref_267_ = lean_ctor_get(v___y_263_, 2);
v_suppressElabErrors_268_ = lean_ctor_get_uint8(v___y_263_, sizeof(void*)*3 + 2);
v_checkDeprecated_269_ = lean_ctor_get_uint8(v___y_263_, sizeof(void*)*3 + 3);
v_isRecordingDeps_270_ = lean_ctor_get_uint8(v___y_263_, sizeof(void*)*3 + 4);
v_isSharedCheck_329_ = !lean_is_exclusive(v___y_263_);
if (v_isSharedCheck_329_ == 0)
{
v___x_272_ = v___y_263_;
v_isShared_273_ = v_isSharedCheck_329_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_ref_267_);
lean_inc(v_currRecDepth_266_);
lean_inc(v_toCold_265_);
lean_dec(v___y_263_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_329_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_fileName_274_; lean_object* v_fileMap_275_; lean_object* v_currNamespace_276_; lean_object* v_openDecls_277_; lean_object* v_initHeartbeats_278_; lean_object* v_maxHeartbeats_279_; lean_object* v_quotContext_280_; lean_object* v_currMacroScope_281_; lean_object* v_cancelTk_x3f_282_; lean_object* v_inheritedTraceOptions_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_326_; 
v_fileName_274_ = lean_ctor_get(v_toCold_265_, 0);
v_fileMap_275_ = lean_ctor_get(v_toCold_265_, 1);
v_currNamespace_276_ = lean_ctor_get(v_toCold_265_, 4);
v_openDecls_277_ = lean_ctor_get(v_toCold_265_, 5);
v_initHeartbeats_278_ = lean_ctor_get(v_toCold_265_, 6);
v_maxHeartbeats_279_ = lean_ctor_get(v_toCold_265_, 7);
v_quotContext_280_ = lean_ctor_get(v_toCold_265_, 8);
v_currMacroScope_281_ = lean_ctor_get(v_toCold_265_, 9);
v_cancelTk_x3f_282_ = lean_ctor_get(v_toCold_265_, 10);
v_inheritedTraceOptions_283_ = lean_ctor_get(v_toCold_265_, 11);
v_isSharedCheck_326_ = !lean_is_exclusive(v_toCold_265_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; lean_object* v_unused_328_; 
v_unused_327_ = lean_ctor_get(v_toCold_265_, 3);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_toCold_265_, 2);
lean_dec(v_unused_328_);
v___x_285_ = v_toCold_265_;
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_inheritedTraceOptions_283_);
lean_inc(v_cancelTk_x3f_282_);
lean_inc(v_currMacroScope_281_);
lean_inc(v_quotContext_280_);
lean_inc(v_maxHeartbeats_279_);
lean_inc(v_initHeartbeats_278_);
lean_inc(v_openDecls_277_);
lean_inc(v_currNamespace_276_);
lean_inc(v_fileMap_275_);
lean_inc(v_fileName_274_);
lean_dec(v_toCold_265_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___y_261_, v___y_260_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 3, v___x_287_);
lean_ctor_set(v___x_285_, 2, v___y_261_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_fileName_274_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_fileMap_275_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___y_261_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_currNamespace_276_);
lean_ctor_set(v_reuseFailAlloc_325_, 5, v_openDecls_277_);
lean_ctor_set(v_reuseFailAlloc_325_, 6, v_initHeartbeats_278_);
lean_ctor_set(v_reuseFailAlloc_325_, 7, v_maxHeartbeats_279_);
lean_ctor_set(v_reuseFailAlloc_325_, 8, v_quotContext_280_);
lean_ctor_set(v_reuseFailAlloc_325_, 9, v_currMacroScope_281_);
lean_ctor_set(v_reuseFailAlloc_325_, 10, v_cancelTk_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_325_, 11, v_inheritedTraceOptions_283_);
v___x_289_ = v_reuseFailAlloc_325_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_291_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_289_);
v___x_291_ = v___x_272_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_currRecDepth_266_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_ref_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*3 + 2, v_suppressElabErrors_268_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*3 + 3, v_checkDeprecated_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*3 + 4, v_isRecordingDeps_270_);
v___x_291_ = v_reuseFailAlloc_324_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
lean_ctor_set_uint16(v___x_291_, sizeof(void*)*3, v___y_262_);
v___x_292_ = lean_apply_3(v_x_222_, v___x_291_, v___y_264_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_st_ref_get(v___x_258_);
lean_dec(v___x_258_);
lean_dec(v___x_297_);
if (v_isShared_296_ == 0)
{
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_293_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_323_; 
lean_dec(v___x_258_);
v_a_302_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_323_ == 0)
{
v___x_304_ = v___x_292_;
v_isShared_305_ = v_isSharedCheck_323_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_292_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_323_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
if (lean_obj_tag(v_a_302_) == 0)
{
lean_object* v_msg_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_msg_306_ = lean_ctor_get(v_a_302_, 1);
lean_inc_ref(v_msg_306_);
lean_dec_ref_known(v_a_302_, 2);
v___x_307_ = l_Lean_MessageData_toString(v_msg_306_);
v___x_308_ = lean_mk_io_user_error(v___x_307_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_308_);
v___x_310_ = v___x_304_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
lean_object* v_id_312_; lean_object* v___x_313_; 
lean_del_object(v___x_304_);
v_id_312_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_id_312_);
lean_dec_ref_known(v_a_302_, 2);
v___x_313_ = l_Lean_InternalExceptionId_getName(v_id_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_id_312_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_313_, 1);
v___x_315_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15));
v___x_316_ = l_Lean_Name_toString(v_a_314_, v___x_254_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v_a_225_ = v___x_317_;
goto v___jp_224_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref_known(v___x_313_, 1);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16));
v___x_319_ = l_Nat_reprFast(v_id_312_);
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_321_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17));
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
v_a_225_ = v___x_322_;
goto v___jp_224_;
}
}
}
}
}
}
}
}
}
v___jp_330_:
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
v___x_337_ = lean_st_ref_take(v___y_333_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_recordedDeps_343_ = lean_ctor_get(v___x_337_, 6);
v_messages_344_ = lean_ctor_get(v___x_337_, 7);
v_infoState_345_ = lean_ctor_get(v___x_337_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_337_, 9);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_356_);
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_Kernel_enableDiag(v_env_338_, v___y_335_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 5, v___x_250_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_354_, 5, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_354_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_354_, 9, v_snapshotTasks_346_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_st_ref_put(v___y_333_, v___x_352_);
v___y_260_ = v___y_331_;
v___y_261_ = v___y_332_;
v___y_262_ = v___y_336_;
v___y_263_ = v___y_334_;
v___y_264_ = v___y_333_;
goto v___jp_259_;
}
}
}
v___jp_357_:
{
uint16_t v___x_362_; lean_object* v___x_363_; lean_object* v_env_364_; uint8_t v___x_365_; uint16_t v___x_366_; uint16_t v___x_367_; uint16_t v___x_368_; uint8_t v___x_369_; 
v___x_362_ = l_Lean_OptionFlags_ofOptions(v___y_361_);
v___x_363_ = lean_st_ref_get(v___y_359_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_364_);
lean_dec_ref(v_env_364_);
v___x_366_ = 512;
v___x_367_ = lean_uint16_land(v___x_362_, v___x_366_);
v___x_368_ = 0;
v___x_369_ = lean_uint16_dec_eq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
if (v___x_365_ == 0)
{
v___y_331_ = v___y_358_;
v___y_332_ = v___y_361_;
v___y_333_ = v___y_359_;
v___y_334_ = v___y_360_;
v___y_335_ = v___x_254_;
v___y_336_ = v___x_362_;
goto v___jp_330_;
}
else
{
v___y_260_ = v___y_358_;
v___y_261_ = v___y_361_;
v___y_262_ = v___x_362_;
v___y_263_ = v___y_360_;
v___y_264_ = v___y_359_;
goto v___jp_259_;
}
}
else
{
if (v___x_365_ == 0)
{
v___y_260_ = v___y_358_;
v___y_261_ = v___y_361_;
v___y_262_ = v___x_362_;
v___y_263_ = v___y_360_;
v___y_264_ = v___y_359_;
goto v___jp_259_;
}
else
{
v___y_331_ = v___y_358_;
v___y_332_ = v___y_361_;
v___y_333_ = v___y_359_;
v___y_334_ = v___y_360_;
v___y_335_ = v___x_234_;
v___y_336_ = v___x_362_;
goto v___jp_330_;
}
}
}
v___jp_370_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = l_Lean_maxRecDepth;
v___x_387_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18);
lean_inc(v_cancelTk_x3f_379_);
lean_inc(v_currMacroScope_378_);
lean_inc(v_quotContext_377_);
lean_inc(v_maxHeartbeats_376_);
lean_inc_ref(v_fileMap_372_);
lean_inc_ref(v_fileName_371_);
v___x_388_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_388_, 0, v_fileName_371_);
lean_ctor_set(v___x_388_, 1, v_fileMap_372_);
lean_ctor_set(v___x_388_, 2, v___x_238_);
lean_ctor_set(v___x_388_, 3, v___x_387_);
lean_ctor_set(v___x_388_, 4, v_currNamespace_373_);
lean_ctor_set(v___x_388_, 5, v_openDecls_374_);
lean_ctor_set(v___x_388_, 6, v_initHeartbeats_375_);
lean_ctor_set(v___x_388_, 7, v_maxHeartbeats_376_);
lean_ctor_set(v___x_388_, 8, v_quotContext_377_);
lean_ctor_set(v___x_388_, 9, v_currMacroScope_378_);
lean_ctor_set(v___x_388_, 10, v_cancelTk_x3f_379_);
lean_ctor_set(v___x_388_, 11, v_inheritedTraceOptions_380_);
lean_inc(v_ref_382_);
v___x_389_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_currRecDepth_381_);
lean_ctor_set(v___x_389_, 2, v_ref_382_);
lean_ctor_set_uint16(v___x_389_, sizeof(void*)*3, v___x_245_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 2, v_suppressElabErrors_383_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 3, v_checkDeprecated_384_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 4, v_isRecordingDeps_385_);
lean_inc(v___x_258_);
v___y_358_ = v___x_386_;
v___y_359_ = v___x_258_;
v___y_360_ = v___x_389_;
v___y_361_ = v_options_230_;
goto v___jp_357_;
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v_nextMacroScope_397_; lean_object* v_ngen_398_; lean_object* v_auxDeclNGen_399_; lean_object* v_traceState_400_; lean_object* v_recordedDeps_401_; lean_object* v_messages_402_; lean_object* v_infoState_403_; lean_object* v_snapshotTasks_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_413_; 
v___x_395_ = lean_st_ref_take(v___x_258_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
v_nextMacroScope_397_ = lean_ctor_get(v___x_395_, 1);
v_ngen_398_ = lean_ctor_get(v___x_395_, 2);
v_auxDeclNGen_399_ = lean_ctor_get(v___x_395_, 3);
v_traceState_400_ = lean_ctor_get(v___x_395_, 4);
v_recordedDeps_401_ = lean_ctor_get(v___x_395_, 6);
v_messages_402_ = lean_ctor_get(v___x_395_, 7);
v_infoState_403_ = lean_ctor_get(v___x_395_, 8);
v_snapshotTasks_404_ = lean_ctor_get(v___x_395_, 9);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_395_, 5);
lean_dec(v_unused_414_);
v___x_406_ = v___x_395_;
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snapshotTasks_404_);
lean_inc(v_infoState_403_);
lean_inc(v_messages_402_);
lean_inc(v_recordedDeps_401_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_399_);
lean_inc(v_ngen_398_);
lean_inc(v_nextMacroScope_397_);
lean_inc(v_env_396_);
lean_dec(v___x_395_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Lean_Kernel_enableDiag(v_env_396_, v___y_394_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 5, v___x_250_);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_nextMacroScope_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_ngen_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_auxDeclNGen_399_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_traceState_400_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_recordedDeps_401_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_messages_402_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_infoState_403_);
lean_ctor_set(v_reuseFailAlloc_412_, 9, v_snapshotTasks_404_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_st_ref_put(v___x_258_, v___x_410_);
v_fileName_371_ = v___x_236_;
v_fileMap_372_ = v___x_237_;
v_currNamespace_373_ = v_currNamespace_231_;
v_openDecls_374_ = v_openDecls_232_;
v_initHeartbeats_375_ = v___x_257_;
v_maxHeartbeats_376_ = v___x_240_;
v_quotContext_377_ = v___x_241_;
v_currMacroScope_378_ = v___x_242_;
v_cancelTk_x3f_379_ = v___x_243_;
v_inheritedTraceOptions_380_ = v___x_391_;
v_currRecDepth_381_ = v___x_239_;
v_ref_382_ = v___x_244_;
v_suppressElabErrors_383_ = v___x_234_;
v_checkDeprecated_384_ = v___x_246_;
v_isRecordingDeps_385_ = v___x_234_;
goto v___jp_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_418_, lean_object* v_x_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_418_, v_x_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_422_, lean_object* v_info_423_, lean_object* v_x_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_423_, v_x_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_427_, lean_object* v_info_428_, lean_object* v_x_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_427_, v_info_428_, v_x_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_432_, lean_object* v_x_433_, lean_object* v___x_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_st_mk_ref(v___x_432_);
lean_inc(v___x_438_);
v___x_439_ = lean_apply_5(v_x_433_, v___x_434_, v___x_438_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = lean_st_ref_get(v___x_438_);
lean_dec(v___x_438_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_a_440_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v___x_438_);
v_a_450_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_439_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_439_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_458_, lean_object* v_x_459_, lean_object* v___x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_458_, v_x_459_, v___x_460_, v___y_461_, v___y_462_);
return v_res_464_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___closed__0);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg();
return v_res_470_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_477_; uint64_t v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_478_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_480_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_481_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set_uint64(v___x_481_, sizeof(void*)*1, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0___redArg();
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
lean_ctor_set(v___x_491_, 2, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_493_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_494_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_495_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_496_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_493_);
lean_ctor_set(v___x_496_, 3, v___x_494_);
lean_ctor_set(v___x_496_, 4, v___x_494_);
lean_ctor_set(v___x_496_, 5, v___x_494_);
lean_ctor_set(v___x_496_, 6, v___x_494_);
lean_ctor_set(v___x_496_, 7, v___x_492_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(32u);
v___x_498_ = lean_mk_empty_array_with_capacity(v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10(void){
_start:
{
size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((size_t)5ULL);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_unsigned_to_nat(32u);
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
v___x_505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_501_);
lean_ctor_set(v___x_505_, 3, v___x_501_);
lean_ctor_set_usize(v___x_505_, 4, v___x_500_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_ctor_set(v___x_507_, 3, v___x_506_);
lean_ctor_set(v___x_507_, 4, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_508_, lean_object* v_lctx_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_toCommandContextInfo_520_; lean_object* v_mctx_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v___x_512_ = lean_box(1);
v___x_513_ = 0;
v___x_514_ = 1;
v___x_515_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_519_, 0, v___x_515_);
lean_ctor_set(v___x_519_, 1, v___x_512_);
lean_ctor_set(v___x_519_, 2, v_lctx_509_);
lean_ctor_set(v___x_519_, 3, v___x_517_);
lean_ctor_set(v___x_519_, 4, v___x_518_);
lean_ctor_set(v___x_519_, 5, v___x_516_);
lean_ctor_set(v___x_519_, 6, v___x_518_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*7, v___x_513_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*7 + 1, v___x_513_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*7 + 2, v___x_513_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*7 + 3, v___x_514_);
v_toCommandContextInfo_520_ = lean_ctor_get(v_info_508_, 0);
v_mctx_521_ = lean_ctor_get(v_toCommandContextInfo_520_, 3);
v___x_522_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_523_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__10);
v___x_524_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__11);
lean_inc_ref(v_mctx_521_);
v___x_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_525_, 0, v_mctx_521_);
lean_ctor_set(v___x_525_, 1, v___x_522_);
lean_ctor_set(v___x_525_, 2, v___x_512_);
lean_ctor_set(v___x_525_, 3, v___x_523_);
lean_ctor_set(v___x_525_, 4, v___x_524_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_526_, 0, v___x_525_);
lean_closure_set(v___f_526_, 1, v_x_510_);
lean_closure_set(v___f_526_, 2, v___x_519_);
v___x_527_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_508_, v___f_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_fst_532_; lean_object* v___x_534_; 
v_fst_532_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_fst_532_);
lean_dec(v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v_fst_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_527_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_527_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_545_, lean_object* v_lctx_546_, lean_object* v_x_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_545_, v_lctx_546_, v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_550_, lean_object* v_info_551_, lean_object* v_lctx_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_551_, v_lctx_552_, v_x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_556_, lean_object* v_info_557_, lean_object* v_lctx_558_, lean_object* v_x_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_556_, v_info_557_, v_lctx_558_, v_x_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0_spec__0(lean_object* v_00_u03b2_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0___redArg(){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0___redArg___boxed(lean_object* v___dummy_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0___redArg();
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ContextInfo_runMetaM_spec__0(lean_object* v_00_u03b2_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_570_, lean_object* v_lctx_571_){
_start:
{
lean_object* v_toCommandContextInfo_572_; lean_object* v_env_573_; lean_object* v_mctx_574_; lean_object* v_options_575_; lean_object* v_currNamespace_576_; lean_object* v_openDecls_577_; lean_object* v___x_578_; 
v_toCommandContextInfo_572_ = lean_ctor_get(v_info_570_, 0);
v_env_573_ = lean_ctor_get(v_toCommandContextInfo_572_, 0);
v_mctx_574_ = lean_ctor_get(v_toCommandContextInfo_572_, 3);
v_options_575_ = lean_ctor_get(v_toCommandContextInfo_572_, 4);
v_currNamespace_576_ = lean_ctor_get(v_toCommandContextInfo_572_, 5);
v_openDecls_577_ = lean_ctor_get(v_toCommandContextInfo_572_, 6);
lean_inc(v_openDecls_577_);
lean_inc(v_currNamespace_576_);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_mctx_574_);
lean_inc_ref(v_env_573_);
v___x_578_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_578_, 0, v_env_573_);
lean_ctor_set(v___x_578_, 1, v_mctx_574_);
lean_ctor_set(v___x_578_, 2, v_lctx_571_);
lean_ctor_set(v___x_578_, 3, v_options_575_);
lean_ctor_set(v___x_578_, 4, v_currNamespace_576_);
lean_ctor_set(v___x_578_, 5, v_openDecls_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_579_, lean_object* v_lctx_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_579_, v_lctx_580_);
lean_dec_ref(v_info_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_582_, lean_object* v_lctx_583_, lean_object* v_stx_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_582_, v_lctx_583_);
v___x_587_ = l_Lean_ppTerm(v___x_586_, v_stx_584_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_589_, lean_object* v_lctx_590_, lean_object* v_stx_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_589_, v_lctx_590_, v_stx_591_);
lean_dec_ref(v_info_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_609_, lean_object* v_pos_610_, lean_object* v_info_611_){
_start:
{
lean_object* v_toCommandContextInfo_612_; lean_object* v_fileMap_613_; lean_object* v___x_614_; lean_object* v_line_615_; lean_object* v_column_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_639_; 
v_toCommandContextInfo_612_ = lean_ctor_get(v_ctx_609_, 0);
lean_inc_ref(v_toCommandContextInfo_612_);
lean_dec_ref(v_ctx_609_);
v_fileMap_613_ = lean_ctor_get(v_toCommandContextInfo_612_, 2);
lean_inc_ref(v_fileMap_613_);
lean_dec_ref(v_toCommandContextInfo_612_);
v___x_614_ = l_Lean_FileMap_toPosition(v_fileMap_613_, v_pos_610_);
v_line_615_ = lean_ctor_get(v___x_614_, 0);
v_column_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_639_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_column_616_);
lean_inc(v_line_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_621_ = l_Nat_reprFast(v_line_615_);
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 5);
lean_ctor_set(v___x_618_, 1, v___x_622_);
lean_ctor_set(v___x_618_, 0, v___x_620_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_638_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_pos_631_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Nat_reprFast(v_column_616_);
v___x_628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_626_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_631_, 0, v___x_629_);
lean_ctor_set(v_pos_631_, 1, v___x_630_);
switch(lean_obj_tag(v_info_611_))
{
case 0:
{
return v_pos_631_;
}
case 1:
{
uint8_t v_canonical_635_; 
v_canonical_635_ = lean_ctor_get_uint8(v_info_611_, sizeof(void*)*2);
if (v_canonical_635_ == 1)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v_pos_631_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
else
{
goto v___jp_632_;
}
}
default: 
{
goto v___jp_632_;
}
}
v___jp_632_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v_pos_631_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_640_, lean_object* v_pos_641_, lean_object* v_info_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_640_, v_pos_641_, v_info_642_);
lean_dec(v_info_642_);
lean_dec(v_pos_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_647_, lean_object* v_stx_648_){
_start:
{
lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___x_659_; lean_object* v___y_661_; lean_object* v___x_664_; 
v___x_659_ = 0;
v___x_664_ = l_Lean_Syntax_getPos_x3f(v_stx_648_, v___x_659_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___y_661_ = v___x_665_;
goto v___jp_660_;
}
else
{
lean_object* v_val_666_; 
v_val_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_664_, 1);
v___y_661_ = v_val_666_;
goto v___jp_660_;
}
v___jp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_652_ = l_Lean_Syntax_getHeadInfo(v_stx_648_);
lean_inc_ref(v_ctx_647_);
v___x_653_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_647_, v___y_650_, v___x_652_);
lean_dec(v___x_652_);
lean_dec(v___y_650_);
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_Syntax_getTailInfo(v_stx_648_);
v___x_657_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_647_, v___y_651_, v___x_656_);
lean_dec(v___x_656_);
lean_dec(v___y_651_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_655_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
return v___x_658_;
}
v___jp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Syntax_getTailPos_x3f(v_stx_648_, v___x_659_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_inc(v___y_661_);
v___y_650_ = v___y_661_;
v___y_651_ = v___y_661_;
goto v___jp_649_;
}
else
{
lean_object* v_val_663_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v___x_662_, 1);
v___y_650_ = v___y_661_;
v___y_651_ = v_val_663_;
goto v___jp_649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_667_, lean_object* v_stx_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_667_, v_stx_668_);
lean_dec(v_stx_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_673_, lean_object* v_info_674_){
_start:
{
lean_object* v_elaborator_675_; lean_object* v_stx_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_691_; 
v_elaborator_675_ = lean_ctor_get(v_info_674_, 0);
v_stx_676_ = lean_ctor_get(v_info_674_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_info_674_);
if (v_isSharedCheck_691_ == 0)
{
v___x_678_ = v_info_674_;
v_isShared_679_ = v_isSharedCheck_691_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_stx_676_);
lean_inc(v_elaborator_675_);
lean_dec(v_info_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_691_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint8_t v___x_680_; 
v___x_680_ = l_Lean_Name_isAnonymous(v_elaborator_675_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_681_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_673_, v_stx_676_);
lean_dec(v_stx_676_);
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 5);
lean_ctor_set(v___x_678_, 1, v___x_682_);
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_689_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = 1;
v___x_686_ = l_Lean_Name_toString(v_elaborator_675_, v___x_685_);
v___x_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_684_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
}
else
{
lean_object* v___x_690_; 
lean_del_object(v___x_678_);
lean_dec(v_elaborator_675_);
v___x_690_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_673_, v_stx_676_);
lean_dec(v_stx_676_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_692_, lean_object* v_ctx_693_, lean_object* v_x_694_){
_start:
{
lean_object* v_lctx_696_; lean_object* v___x_697_; 
v_lctx_696_ = lean_ctor_get(v_info_692_, 1);
lean_inc_ref(v_lctx_696_);
lean_dec_ref(v_info_692_);
v___x_697_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_693_, v_lctx_696_, v_x_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_698_, lean_object* v_ctx_699_, lean_object* v_x_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_698_, v_ctx_699_, v_x_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_703_, lean_object* v_info_704_, lean_object* v_ctx_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_704_, v_ctx_705_, v_x_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_709_, lean_object* v_info_710_, lean_object* v_ctx_711_, lean_object* v_x_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_709_, v_info_710_, v_ctx_711_, v_x_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_729_, lean_object* v_toElabInfo_730_, lean_object* v_expr_731_, uint8_t v_isBinder_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v_a_753_; lean_object* v___y_763_; lean_object* v_a_764_; lean_object* v___x_768_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc_ref(v_expr_731_);
v___x_768_ = lean_infer_type(v_expr_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Meta_ppExpr(v_a_769_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v_a_753_ = v_a_771_;
goto v___jp_752_;
}
else
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_772_);
v___y_763_ = v___x_770_;
v_a_764_ = v_a_772_;
goto v___jp_762_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
lean_inc(v_a_773_);
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v___y_763_ = v___x_778_;
v_a_764_ = v_a_773_;
goto v___jp_762_;
}
}
}
v___jp_738_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc_ref(v___y_741_);
v___x_742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_742_, 0, v___y_741_);
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___y_740_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___y_739_);
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_729_, v_toElabInfo_730_);
v___x_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
v___jp_752_:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_ppExpr(v_expr_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v_a_755_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
if (v_isBinder_732_ == 0)
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_739_ = v_a_753_;
v___y_740_ = v___x_759_;
v___y_741_ = v___x_760_;
goto v___jp_738_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_739_ = v_a_753_;
v___y_740_ = v___x_759_;
v___y_741_ = v___x_761_;
goto v___jp_738_;
}
}
else
{
lean_dec(v_a_753_);
lean_dec_ref(v_toElabInfo_730_);
lean_dec_ref(v_ctx_729_);
return v___x_754_;
}
}
v___jp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = l_Lean_Exception_isInterrupt(v_a_764_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; 
v___x_766_ = l_Lean_Exception_isRuntime(v_a_764_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v___y_763_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_753_ = v___x_767_;
goto v___jp_752_;
}
else
{
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec_ref(v_expr_731_);
lean_dec_ref(v_toElabInfo_730_);
lean_dec_ref(v_ctx_729_);
return v___y_763_;
}
}
else
{
lean_dec_ref(v_a_764_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec_ref(v_expr_731_);
lean_dec_ref(v_toElabInfo_730_);
lean_dec_ref(v_ctx_729_);
return v___y_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_781_, lean_object* v_toElabInfo_782_, lean_object* v_expr_783_, lean_object* v_isBinder_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v_isBinder_boxed_790_; lean_object* v_res_791_; 
v_isBinder_boxed_790_ = lean_unbox(v_isBinder_784_);
v_res_791_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_781_, v_toElabInfo_782_, v_expr_783_, v_isBinder_boxed_790_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_792_, lean_object* v_info_793_){
_start:
{
lean_object* v_toElabInfo_795_; lean_object* v_expr_796_; uint8_t v_isBinder_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___x_800_; 
v_toElabInfo_795_ = lean_ctor_get(v_info_793_, 0);
v_expr_796_ = lean_ctor_get(v_info_793_, 3);
v_isBinder_797_ = lean_ctor_get_uint8(v_info_793_, sizeof(void*)*4);
v___x_798_ = lean_box(v_isBinder_797_);
lean_inc_ref(v_expr_796_);
lean_inc_ref(v_toElabInfo_795_);
lean_inc_ref(v_ctx_792_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_799_, 0, v_ctx_792_);
lean_closure_set(v___f_799_, 1, v_toElabInfo_795_);
lean_closure_set(v___f_799_, 2, v_expr_796_);
lean_closure_set(v___f_799_, 3, v___x_798_);
v___x_800_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_793_, v_ctx_792_, v___f_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_801_, lean_object* v_info_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Elab_TermInfo_format(v_ctx_801_, v_info_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_808_, lean_object* v_info_809_){
_start:
{
lean_object* v_toElabInfo_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_toElabInfo_810_ = lean_ctor_get(v_info_809_, 0);
lean_inc_ref(v_toElabInfo_810_);
lean_dec_ref(v_info_809_);
v___x_811_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_812_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_808_, v_toElabInfo_810_);
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_821_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_832_; 
v_val_822_ = lean_ctor_get(v_x_820_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_832_ == 0)
{
v___x_824_ = v_x_820_;
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v_x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_827_ = lean_expr_dbg_to_string(v_val_822_);
lean_dec(v_val_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 3);
lean_ctor_set(v___x_824_, 0, v___x_827_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_826_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_839_, lean_object* v_lctx_840_, lean_object* v_stx_841_, lean_object* v_expectedType_x3f_842_, lean_object* v_info_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_868_; 
v___x_849_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_839_, v_lctx_840_, v_stx_841_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_854_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_a_850_);
v___x_856_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_842_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_Elab_CompletionInfo_stx(v_info_843_);
v___x_863_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_839_, v___x_862_);
lean_dec(v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_864_);
v___x_866_ = v___x_852_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_869_, lean_object* v_lctx_870_, lean_object* v_stx_871_, lean_object* v_expectedType_x3f_872_, lean_object* v_info_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_869_, v_lctx_870_, v_stx_871_, v_expectedType_x3f_872_, v_info_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v_info_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_886_, lean_object* v_info_887_){
_start:
{
switch(lean_obj_tag(v_info_887_))
{
case 0:
{
lean_object* v_termInfo_889_; lean_object* v_expectedType_x3f_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_911_; 
v_termInfo_889_ = lean_ctor_get(v_info_887_, 0);
v_expectedType_x3f_890_ = lean_ctor_get(v_info_887_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_info_887_);
if (v_isSharedCheck_911_ == 0)
{
v___x_892_ = v_info_887_;
v_isShared_893_ = v_isSharedCheck_911_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_expectedType_x3f_890_);
lean_inc(v_termInfo_889_);
lean_dec(v_info_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_911_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Elab_TermInfo_format(v_ctx_886_, v_termInfo_889_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_910_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_910_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 5);
lean_ctor_set(v___x_892_, 1, v_a_895_);
lean_ctor_set(v___x_892_, 0, v___x_899_);
v___x_901_ = v___x_892_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_895_);
v___x_901_ = v_reuseFailAlloc_909_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_890_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_905_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_del_object(v___x_892_);
lean_dec(v_expectedType_x3f_890_);
return v___x_894_;
}
}
}
case 1:
{
lean_object* v_stx_912_; lean_object* v_lctx_913_; lean_object* v_expectedType_x3f_914_; lean_object* v___f_915_; lean_object* v___x_916_; 
v_stx_912_ = lean_ctor_get(v_info_887_, 0);
lean_inc(v_stx_912_);
v_lctx_913_ = lean_ctor_get(v_info_887_, 2);
lean_inc_ref_n(v_lctx_913_, 2);
v_expectedType_x3f_914_ = lean_ctor_get(v_info_887_, 3);
lean_inc(v_expectedType_x3f_914_);
lean_inc_ref(v_ctx_886_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_915_, 0, v_ctx_886_);
lean_closure_set(v___f_915_, 1, v_lctx_913_);
lean_closure_set(v___f_915_, 2, v_stx_912_);
lean_closure_set(v___f_915_, 3, v_expectedType_x3f_914_);
lean_closure_set(v___f_915_, 4, v_info_887_);
v___x_916_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_886_, v_lctx_913_, v___f_915_);
return v___x_916_;
}
default: 
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_917_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_918_ = l_Lean_Elab_CompletionInfo_stx(v_info_887_);
lean_dec_ref(v_info_887_);
v___x_919_ = lean_box(0);
v___x_920_ = 0;
lean_inc(v___x_918_);
v___x_921_ = l_Lean_Syntax_formatStx(v___x_918_, v___x_919_, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_917_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_886_, v___x_918_);
lean_dec(v___x_918_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_928_, lean_object* v_info_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Elab_CompletionInfo_format(v_ctx_928_, v_info_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_935_, lean_object* v_info_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_939_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_935_, v_info_936_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_942_, lean_object* v_info_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Elab_CommandInfo_format(v_ctx_942_, v_info_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_949_, lean_object* v_info_950_){
_start:
{
lean_object* v_stx_952_; lean_object* v_optionName_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_stx_952_ = lean_ctor_get(v_info_950_, 0);
lean_inc(v_stx_952_);
v_optionName_953_ = lean_ctor_get(v_info_950_, 1);
lean_inc(v_optionName_953_);
lean_dec_ref(v_info_950_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_955_ = 1;
v___x_956_ = l_Lean_Name_toString(v_optionName_953_, v___x_955_);
v___x_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_954_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_949_, v_stx_952_);
lean_dec(v_stx_952_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_964_, lean_object* v_info_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Elab_OptionInfo_format(v_ctx_964_, v_info_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_971_, lean_object* v_info_972_){
_start:
{
lean_object* v_stx_974_; lean_object* v_errorName_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_991_; 
v_stx_974_ = lean_ctor_get(v_info_972_, 0);
v_errorName_975_ = lean_ctor_get(v_info_972_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_info_972_);
if (v_isSharedCheck_991_ == 0)
{
v___x_977_ = v_info_972_;
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_errorName_975_);
lean_inc(v_stx_974_);
lean_dec(v_info_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_980_ = 1;
v___x_981_ = l_Lean_Name_toString(v_errorName_975_, v___x_980_);
v___x_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 5);
lean_ctor_set(v___x_977_, 1, v___x_982_);
lean_ctor_set(v___x_977_, 0, v___x_979_);
v___x_984_ = v___x_977_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_990_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_985_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_971_, v_stx_974_);
lean_dec(v_stx_974_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_992_, lean_object* v_info_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_992_, v_info_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_1002_, lean_object* v_fieldName_1003_, lean_object* v_ctx_1004_, lean_object* v_stx_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc_ref(v_val_1002_);
v___x_1011_ = lean_infer_type(v_val_1002_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_Meta_ppExpr(v_a_1012_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1044_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1044_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1044_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_ppExpr(v_val_1002_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1043_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1043_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1043_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1023_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1024_ = 1;
v___x_1025_ = l_Lean_Name_toString(v_fieldName_1003_, v___x_1024_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 3);
lean_ctor_set(v___x_1016_, 0, v___x_1025_);
v___x_1027_ = v___x_1016_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_1014_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_a_1019_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1004_, v_stx_1005_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1038_);
v___x_1040_ = v___x_1021_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_del_object(v___x_1016_);
lean_dec(v_a_1014_);
lean_dec_ref(v_ctx_1004_);
lean_dec(v_fieldName_1003_);
return v___x_1018_;
}
}
}
else
{
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_ctx_1004_);
lean_dec(v_fieldName_1003_);
lean_dec_ref(v_val_1002_);
return v___x_1013_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_ctx_1004_);
lean_dec(v_fieldName_1003_);
lean_dec_ref(v_val_1002_);
v_a_1045_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1011_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1011_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1053_, lean_object* v_fieldName_1054_, lean_object* v_ctx_1055_, lean_object* v_stx_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1053_, v_fieldName_1054_, v_ctx_1055_, v_stx_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v_stx_1056_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1063_, lean_object* v_info_1064_){
_start:
{
lean_object* v_fieldName_1066_; lean_object* v_lctx_1067_; lean_object* v_val_1068_; lean_object* v_stx_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v_fieldName_1066_ = lean_ctor_get(v_info_1064_, 1);
lean_inc(v_fieldName_1066_);
v_lctx_1067_ = lean_ctor_get(v_info_1064_, 2);
lean_inc_ref(v_lctx_1067_);
v_val_1068_ = lean_ctor_get(v_info_1064_, 3);
lean_inc_ref(v_val_1068_);
v_stx_1069_ = lean_ctor_get(v_info_1064_, 4);
lean_inc(v_stx_1069_);
lean_dec_ref(v_info_1064_);
lean_inc_ref(v_ctx_1063_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1070_, 0, v_val_1068_);
lean_closure_set(v___f_1070_, 1, v_fieldName_1066_);
lean_closure_set(v___f_1070_, 2, v_ctx_1063_);
lean_closure_set(v___f_1070_, 3, v_stx_1069_);
v___x_1071_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1063_, v_lctx_1067_, v___f_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1072_, lean_object* v_info_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Elab_FieldInfo_format(v_ctx_1072_, v_info_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_dec(v_pre_1076_);
return v_x_1077_;
}
else
{
lean_object* v_head_1079_; lean_object* v_tail_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
v_head_1079_ = lean_ctor_get(v_x_1078_, 0);
v_tail_1080_ = lean_ctor_get(v_x_1078_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v_x_1078_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_tail_1080_);
lean_inc(v_head_1079_);
lean_dec(v_x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
lean_inc(v_pre_1076_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 5);
lean_ctor_set(v___x_1082_, 1, v_pre_1076_);
lean_ctor_set(v___x_1082_, 0, v_x_1077_);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_x_1077_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_pre_1076_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_head_1079_);
v_x_1077_ = v___x_1086_;
v_x_1078_ = v_tail_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v___x_1092_; 
lean_dec(v_pre_1090_);
v___x_1092_ = lean_box(0);
return v___x_1092_;
}
else
{
lean_object* v_head_1093_; lean_object* v_tail_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_head_1093_ = lean_ctor_get(v_x_1091_, 0);
v_tail_1094_ = lean_ctor_get(v_x_1091_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v_x_1091_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_tail_1094_);
lean_inc(v_head_1093_);
lean_dec(v_x_1091_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
lean_inc(v_pre_1090_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 5);
lean_ctor_set(v___x_1096_, 1, v_head_1093_);
lean_ctor_set(v___x_1096_, 0, v_pre_1090_);
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_pre_1090_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_head_1093_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1090_, v___x_1099_, v_tail_1094_);
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_List_reverse___redArg(v_x_1104_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_head_1112_; lean_object* v_tail_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1131_; 
v_head_1112_ = lean_ctor_get(v_x_1103_, 0);
v_tail_1113_ = lean_ctor_get(v_x_1103_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1103_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1115_ = v_x_1103_;
v_isShared_1116_ = v_isSharedCheck_1131_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_tail_1113_);
lean_inc(v_head_1112_);
lean_dec(v_x_1103_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1131_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_ppGoal(v_head_1112_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v_head_1112_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_x_1104_);
lean_ctor_set(v___x_1115_, 0, v_a_1118_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1118_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_x_1104_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v_x_1103_ = v_tail_1113_;
v_x_1104_ = v___x_1120_;
goto _start;
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_del_object(v___x_1115_);
lean_dec(v_tail_1113_);
lean_dec(v_x_1104_);
v_a_1123_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1117_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1132_, v_x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1143_, lean_object* v___x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1143_, v___x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1160_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1155_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1156_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1155_, v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1156_);
v___x_1158_ = v___x_1153_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1150_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1150_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1169_, lean_object* v___x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1169_, v___x_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1176_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(32u);
v___x_1180_ = lean_mk_empty_array_with_capacity(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1182_ = ((size_t)5ULL);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_unsigned_to_nat(32u);
v___x_1185_ = lean_mk_empty_array_with_capacity(v___x_1184_);
v___x_1186_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
lean_ctor_set(v___x_1187_, 2, v___x_1183_);
lean_ctor_set(v___x_1187_, 3, v___x_1183_);
lean_ctor_set_usize(v___x_1187_, 4, v___x_1182_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_box(1);
v___x_1189_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1190_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___x_1189_);
lean_ctor_set(v___x_1191_, 2, v___x_1188_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1195_, lean_object* v_goals_1196_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_List_isEmpty___redArg(v_goals_1196_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v___x_1199_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1200_ = lean_box(0);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1201_, 0, v_goals_1196_);
lean_closure_set(v___f_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1195_, v___x_1199_, v___f_1201_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v_goals_1196_);
lean_dec_ref(v_ctx_1195_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1205_, lean_object* v_goals_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1205_, v_goals_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1218_, lean_object* v_info_1219_){
_start:
{
lean_object* v_toCommandContextInfo_1221_; lean_object* v_parentDecl_x3f_1222_; lean_object* v_autoImplicits_1223_; lean_object* v_env_1224_; lean_object* v_cmdEnv_x3f_1225_; lean_object* v_fileMap_1226_; lean_object* v_options_1227_; lean_object* v_currNamespace_1228_; lean_object* v_openDecls_1229_; lean_object* v_ngen_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1272_; 
v_toCommandContextInfo_1221_ = lean_ctor_get(v_ctx_1218_, 0);
lean_inc_ref(v_toCommandContextInfo_1221_);
v_parentDecl_x3f_1222_ = lean_ctor_get(v_ctx_1218_, 1);
v_autoImplicits_1223_ = lean_ctor_get(v_ctx_1218_, 2);
v_env_1224_ = lean_ctor_get(v_toCommandContextInfo_1221_, 0);
v_cmdEnv_x3f_1225_ = lean_ctor_get(v_toCommandContextInfo_1221_, 1);
v_fileMap_1226_ = lean_ctor_get(v_toCommandContextInfo_1221_, 2);
v_options_1227_ = lean_ctor_get(v_toCommandContextInfo_1221_, 4);
v_currNamespace_1228_ = lean_ctor_get(v_toCommandContextInfo_1221_, 5);
v_openDecls_1229_ = lean_ctor_get(v_toCommandContextInfo_1221_, 6);
v_ngen_1230_ = lean_ctor_get(v_toCommandContextInfo_1221_, 7);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_toCommandContextInfo_1221_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v_toCommandContextInfo_1221_, 3);
lean_dec(v_unused_1273_);
v___x_1232_ = v_toCommandContextInfo_1221_;
v_isShared_1233_ = v_isSharedCheck_1272_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_ngen_1230_);
lean_inc(v_openDecls_1229_);
lean_inc(v_currNamespace_1228_);
lean_inc(v_options_1227_);
lean_inc(v_fileMap_1226_);
lean_inc(v_cmdEnv_x3f_1225_);
lean_inc(v_env_1224_);
lean_dec(v_toCommandContextInfo_1221_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1272_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_toElabInfo_1234_; lean_object* v_mctxBefore_1235_; lean_object* v_goalsBefore_1236_; lean_object* v_mctxAfter_1237_; lean_object* v_goalsAfter_1238_; lean_object* v___x_1240_; 
v_toElabInfo_1234_ = lean_ctor_get(v_info_1219_, 0);
lean_inc_ref(v_toElabInfo_1234_);
v_mctxBefore_1235_ = lean_ctor_get(v_info_1219_, 1);
lean_inc_ref(v_mctxBefore_1235_);
v_goalsBefore_1236_ = lean_ctor_get(v_info_1219_, 2);
lean_inc(v_goalsBefore_1236_);
v_mctxAfter_1237_ = lean_ctor_get(v_info_1219_, 3);
lean_inc_ref(v_mctxAfter_1237_);
v_goalsAfter_1238_ = lean_ctor_get(v_info_1219_, 4);
lean_inc(v_goalsAfter_1238_);
lean_dec_ref(v_info_1219_);
lean_inc_ref(v_ngen_1230_);
lean_inc(v_openDecls_1229_);
lean_inc(v_currNamespace_1228_);
lean_inc_ref(v_options_1227_);
lean_inc_ref(v_fileMap_1226_);
lean_inc(v_cmdEnv_x3f_1225_);
lean_inc_ref(v_env_1224_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v_mctxBefore_1235_);
v___x_1240_ = v___x_1232_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_env_1224_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_cmdEnv_x3f_1225_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_fileMap_1226_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_mctxBefore_1235_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_options_1227_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v_currNamespace_1228_);
lean_ctor_set(v_reuseFailAlloc_1271_, 6, v_openDecls_1229_);
lean_ctor_set(v_reuseFailAlloc_1271_, 7, v_ngen_1230_);
v___x_1240_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v_ctxB_1241_; lean_object* v___x_1242_; lean_object* v_ctxA_1243_; lean_object* v___x_1244_; 
lean_inc_ref_n(v_autoImplicits_1223_, 2);
lean_inc_n(v_parentDecl_x3f_1222_, 2);
v_ctxB_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1241_, 0, v___x_1240_);
lean_ctor_set(v_ctxB_1241_, 1, v_parentDecl_x3f_1222_);
lean_ctor_set(v_ctxB_1241_, 2, v_autoImplicits_1223_);
v___x_1242_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1242_, 0, v_env_1224_);
lean_ctor_set(v___x_1242_, 1, v_cmdEnv_x3f_1225_);
lean_ctor_set(v___x_1242_, 2, v_fileMap_1226_);
lean_ctor_set(v___x_1242_, 3, v_mctxAfter_1237_);
lean_ctor_set(v___x_1242_, 4, v_options_1227_);
lean_ctor_set(v___x_1242_, 5, v_currNamespace_1228_);
lean_ctor_set(v___x_1242_, 6, v_openDecls_1229_);
lean_ctor_set(v___x_1242_, 7, v_ngen_1230_);
v_ctxA_1243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1243_, 0, v___x_1242_);
lean_ctor_set(v_ctxA_1243_, 1, v_parentDecl_x3f_1222_);
lean_ctor_set(v_ctxA_1243_, 2, v_autoImplicits_1223_);
v___x_1244_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1241_, v_goalsBefore_1236_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1243_, v_goalsAfter_1238_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1270_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1270_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1270_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_stx_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v_stx_1251_ = lean_ctor_get(v_toElabInfo_1234_, 1);
lean_inc(v_stx_1251_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1253_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1218_, v_toElabInfo_1234_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_box(0);
v___x_1258_ = 0;
v___x_1259_ = l_Lean_Syntax_formatStx(v_stx_1251_, v___x_1257_, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1256_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v_a_1245_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1266_);
v___x_1268_ = v___x_1249_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_dec(v_a_1245_);
lean_dec_ref(v_toElabInfo_1234_);
lean_dec_ref(v_ctx_1218_);
return v___x_1246_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1243_, 3);
lean_dec(v_goalsAfter_1238_);
lean_dec_ref(v_toElabInfo_1234_);
lean_dec_ref(v_ctx_1218_);
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1274_, lean_object* v_info_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Elab_TacticInfo_format(v_ctx_1274_, v_info_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1284_, lean_object* v_info_1285_){
_start:
{
lean_object* v_lctx_1287_; lean_object* v_stx_1288_; lean_object* v_output_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1305_; 
v_lctx_1287_ = lean_ctor_get(v_info_1285_, 0);
lean_inc_ref_n(v_lctx_1287_, 2);
v_stx_1288_ = lean_ctor_get(v_info_1285_, 1);
lean_inc(v_stx_1288_);
v_output_1289_ = lean_ctor_get(v_info_1285_, 2);
lean_inc(v_output_1289_);
lean_dec_ref(v_info_1285_);
v___x_1290_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1284_, v_lctx_1287_, v_stx_1288_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v___x_1290_);
v___x_1292_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1284_, v_lctx_1287_, v_output_1289_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1297_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v_a_1291_);
v___x_1299_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1293_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1301_);
v___x_1303_ = v___x_1295_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1306_, lean_object* v_info_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1306_, v_info_1307_);
lean_dec_ref(v_ctx_1306_);
return v_res_1309_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = 1;
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1315_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set_usize(v___x_1315_, 2, v___x_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3, v___x_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1319_){
_start:
{
lean_object* v_toWidgetInstance_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1349_; 
v_toWidgetInstance_1320_ = lean_ctor_get(v_info_1319_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_info_1319_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_info_1319_, 1);
lean_dec(v_unused_1350_);
v___x_1322_ = v_info_1319_;
v_isShared_1323_ = v_isSharedCheck_1349_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_toWidgetInstance_1320_);
lean_dec(v_info_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1349_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_id_1324_; lean_object* v_props_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_fst_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1347_; 
v_id_1324_ = lean_ctor_get(v_toWidgetInstance_1320_, 0);
lean_inc(v_id_1324_);
v_props_1325_ = lean_ctor_get(v_toWidgetInstance_1320_, 1);
lean_inc_ref(v_props_1325_);
lean_dec_ref(v_toWidgetInstance_1320_);
v___x_1326_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1327_ = lean_apply_1(v_props_1325_, v___x_1326_);
v_fst_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1327_, 1);
lean_dec(v_unused_1348_);
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1347_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_fst_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1347_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1332_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1333_ = 1;
v___x_1334_ = l_Lean_Name_toString(v_id_1324_, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 5);
lean_ctor_set(v___x_1330_, 1, v___x_1335_);
lean_ctor_set(v___x_1330_, 0, v___x_1332_);
v___x_1337_ = v___x_1330_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 5);
lean_ctor_set(v___x_1322_, 1, v___x_1338_);
lean_ctor_set(v___x_1322_, 0, v___x_1337_);
v___x_1340_ = v___x_1322_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1341_ = lean_unsigned_to_nat(80u);
v___x_1342_ = l_Lean_Json_pretty(v_fst_1328_, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1357_){
_start:
{
lean_object* v_userName_1358_; lean_object* v_id_1359_; lean_object* v_baseId_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_userName_1358_ = lean_ctor_get(v_info_1357_, 0);
lean_inc(v_userName_1358_);
v_id_1359_ = lean_ctor_get(v_info_1357_, 1);
lean_inc(v_id_1359_);
v_baseId_1360_ = lean_ctor_get(v_info_1357_, 2);
lean_inc(v_baseId_1360_);
lean_dec_ref(v_info_1357_);
v___x_1361_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1362_ = l_Lean_Name_eraseMacroScopes(v_userName_1358_);
lean_dec(v_userName_1358_);
v___x_1363_ = 1;
v___x_1364_ = l_Lean_Name_toString(v___x_1362_, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1361_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_Name_toString(v_id_1359_, v___x_1363_);
v___x_1370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1368_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_Name_toString(v_baseId_1360_, v___x_1363_);
v___x_1375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1380_, lean_object* v_info_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1383_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1380_, v_info_1381_);
v___x_1384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1385_, lean_object* v_info_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1385_, v_info_1386_);
lean_dec(v_info_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1390_, lean_object* v_info_1391_){
_start:
{
lean_object* v_mkDocString_x3f_1393_; 
v_mkDocString_x3f_1393_ = lean_ctor_get(v_info_1391_, 2);
lean_inc(v_mkDocString_x3f_1393_);
lean_dec_ref(v_info_1391_);
if (lean_obj_tag(v_mkDocString_x3f_1393_) == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_ppCtx_1390_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
else
{
lean_object* v_val_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1428_; 
v_val_1396_ = lean_ctor_get(v_mkDocString_x3f_1393_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_mkDocString_x3f_1393_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1398_ = v_mkDocString_x3f_1393_;
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_val_1396_);
lean_dec(v_mkDocString_x3f_1393_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_apply_2(v_val_1396_, v_ppCtx_1390_, lean_box(0));
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_a_1401_);
v___x_1406_ = v___x_1398_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1427_; 
v_a_1412_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1414_ = v___x_1400_;
v_isShared_1415_ = v_isSharedCheck_1427_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1400_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1427_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1416_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1417_ = lean_io_error_to_string(v_a_1412_);
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1420_ = lean_string_append(v___x_1418_, v___x_1419_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1420_);
v___x_1422_ = v___x_1398_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1422_);
v___x_1424_ = v___x_1414_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1429_, lean_object* v_info_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1429_, v_info_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1435_;
}
else
{
lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1447_; 
v_val_1436_ = lean_ctor_get(v_x_1433_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1433_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1438_ = v_x_1433_;
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_dec(v_x_1433_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1441_ = l_String_quote(v_val_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 3);
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Repr_addAppParen(v___x_1444_, v_x_1434_);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1465_, lean_object* v_info_1466_){
_start:
{
lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v_toTermInfo_1474_; lean_object* v_location_x3f_1475_; uint8_t v_explicit_1476_; lean_object* v___y_1478_; 
v_toTermInfo_1474_ = lean_ctor_get(v_info_1466_, 0);
lean_inc_ref(v_toTermInfo_1474_);
v_location_x3f_1475_ = lean_ctor_get(v_info_1466_, 1);
lean_inc(v_location_x3f_1475_);
v_explicit_1476_ = lean_ctor_get_uint8(v_info_1466_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1475_) == 1)
{
lean_object* v_val_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1560_; 
v_val_1499_ = lean_ctor_get(v_location_x3f_1475_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_location_x3f_1475_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1501_ = v_location_x3f_1475_;
v_isShared_1502_ = v_isSharedCheck_1560_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_val_1499_);
lean_dec(v_location_x3f_1475_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1560_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_range_1503_; lean_object* v_pos_1504_; lean_object* v_endPos_1505_; lean_object* v_module_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1558_; 
v_range_1503_ = lean_ctor_get(v_val_1499_, 1);
v_pos_1504_ = lean_ctor_get(v_range_1503_, 0);
lean_inc_ref(v_pos_1504_);
v_endPos_1505_ = lean_ctor_get(v_range_1503_, 2);
lean_inc_ref(v_endPos_1505_);
v_module_1506_ = lean_ctor_get(v_val_1499_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_val_1499_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_val_1499_, 1);
lean_dec(v_unused_1559_);
v___x_1508_ = v_val_1499_;
v_isShared_1509_ = v_isSharedCheck_1558_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_module_1506_);
lean_dec(v_val_1499_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1558_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_line_1510_; lean_object* v_column_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1557_; 
v_line_1510_ = lean_ctor_get(v_pos_1504_, 0);
v_column_1511_ = lean_ctor_get(v_pos_1504_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_pos_1504_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1513_ = v_pos_1504_;
v_isShared_1514_ = v_isSharedCheck_1557_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_column_1511_);
lean_inc(v_line_1510_);
lean_dec(v_pos_1504_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1557_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_line_1515_; lean_object* v_column_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1556_; 
v_line_1515_ = lean_ctor_get(v_endPos_1505_, 0);
v_column_1516_ = lean_ctor_get(v_endPos_1505_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_endPos_1505_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1518_ = v_endPos_1505_;
v_isShared_1519_ = v_isSharedCheck_1556_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_column_1516_);
lean_inc(v_line_1515_);
lean_dec(v_endPos_1505_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1556_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = 1;
v___x_1521_ = l_Lean_Name_toString(v_module_1506_, v___x_1520_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 3);
lean_ctor_set(v___x_1501_, 0, v___x_1521_);
v___x_1523_ = v___x_1501_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 5);
lean_ctor_set(v___x_1518_, 1, v___x_1524_);
lean_ctor_set(v___x_1518_, 0, v___x_1523_);
v___x_1526_ = v___x_1518_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1528_ = l_Nat_reprFast(v_line_1510_);
v___x_1529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set_tag(v___x_1513_, 5);
lean_ctor_set(v___x_1513_, 1, v___x_1529_);
lean_ctor_set(v___x_1513_, 0, v___x_1527_);
v___x_1531_ = v___x_1513_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 5);
lean_ctor_set(v___x_1508_, 1, v___x_1532_);
lean_ctor_set(v___x_1508_, 0, v___x_1531_);
v___x_1534_ = v___x_1508_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1535_ = l_Nat_reprFast(v_column_1511_);
v___x_1536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1526_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = l_Nat_reprFast(v_line_1515_);
v___x_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1527_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1532_);
v___x_1547_ = l_Nat_reprFast(v_column_1516_);
v___x_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1538_);
v___x_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1542_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___y_1478_ = v___x_1551_;
goto v___jp_1477_;
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
lean_object* v___x_1561_; 
lean_dec(v_location_x3f_1475_);
v___x_1561_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1478_ = v___x_1561_;
goto v___jp_1477_;
}
v___jp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1470_);
v___x_1471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1470_);
v___x_1472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1469_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
v___jp_1477_:
{
lean_object* v_lctx_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_lctx_1479_ = lean_ctor_get(v_toTermInfo_1474_, 1);
lean_inc_ref(v_lctx_1479_);
v___x_1480_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1465_, v_lctx_1479_);
v___x_1481_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1480_, v_info_1466_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = l_Lean_Elab_TermInfo_format(v_ctx_1465_, v_toTermInfo_1474_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_a_1484_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___y_1478_);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1482_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1491_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
if (v_explicit_1476_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1469_ = v___x_1496_;
v___y_1470_ = v___x_1497_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1498_; 
v___x_1498_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1469_ = v___x_1496_;
v___y_1470_ = v___x_1498_;
goto v___jp_1468_;
}
}
else
{
lean_dec(v_a_1482_);
lean_dec(v___y_1478_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1562_, lean_object* v_info_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1562_, v_info_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1569_, lean_object* v_info_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1572_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1569_, v_info_1570_);
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1586_, lean_object* v_info_1587_){
_start:
{
lean_object* v_stx_1588_; lean_object* v_chosenAltIdx_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1617_; 
v_stx_1588_ = lean_ctor_get(v_info_1587_, 0);
v_chosenAltIdx_1589_ = lean_ctor_get(v_info_1587_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_info_1587_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1591_ = v_info_1587_;
v_isShared_1592_ = v_isSharedCheck_1617_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_chosenAltIdx_1589_);
lean_inc(v_stx_1588_);
lean_dec(v_info_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1617_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1593_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1589_);
v___x_1594_ = l_Nat_reprFast(v_chosenAltIdx_1589_);
v___x_1595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 5);
lean_ctor_set(v___x_1591_, 1, v___x_1595_);
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1597_ = v___x_1591_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1598_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_Syntax_getNumArgs(v_stx_1588_);
v___x_1601_ = l_Nat_reprFast(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1599_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = l_Lean_Syntax_getArg(v_stx_1588_, v_chosenAltIdx_1589_);
lean_dec(v_chosenAltIdx_1589_);
v___x_1607_ = l_Lean_Syntax_getKind(v___x_1606_);
v___x_1608_ = 1;
v___x_1609_ = l_Lean_Name_toString(v___x_1607_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1605_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1586_, v_stx_1588_);
lean_dec(v_stx_1588_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1621_, lean_object* v_info_1622_){
_start:
{
lean_object* v_stx_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_stx_1623_ = lean_ctor_get(v_info_1622_, 1);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1623_);
v___x_1625_ = l_Lean_Syntax_getKind(v_stx_1623_);
v___x_1626_ = 1;
v___x_1627_ = l_Lean_Name_toString(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1624_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1621_, v_info_1622_);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1637_, lean_object* v_info_1638_){
_start:
{
lean_object* v_toElabInfo_1639_; lean_object* v_name_1640_; uint8_t v_kind_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_toElabInfo_1639_ = lean_ctor_get(v_info_1638_, 0);
lean_inc_ref(v_toElabInfo_1639_);
v_name_1640_ = lean_ctor_get(v_info_1638_, 1);
lean_inc(v_name_1640_);
v_kind_1641_ = lean_ctor_get_uint8(v_info_1638_, sizeof(void*)*2);
lean_dec_ref(v_info_1638_);
v___x_1642_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1643_ = 1;
v___x_1644_ = l_Lean_Name_toString(v_name_1640_, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1642_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1641_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1637_, v_toElabInfo_1639_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1656_, lean_object* v_x_1657_){
_start:
{
switch(lean_obj_tag(v_x_1657_))
{
case 0:
{
lean_object* v_i_1659_; lean_object* v___x_1660_; 
v_i_1659_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1659_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1660_ = l_Lean_Elab_TacticInfo_format(v_ctx_1656_, v_i_1659_);
return v___x_1660_;
}
case 1:
{
lean_object* v_i_1661_; lean_object* v___x_1662_; 
v_i_1661_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1661_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1662_ = l_Lean_Elab_TermInfo_format(v_ctx_1656_, v_i_1661_);
return v___x_1662_;
}
case 2:
{
lean_object* v_i_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1671_; 
v_i_1663_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1665_ = v_x_1657_;
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_i_1663_);
lean_dec(v_x_1657_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1656_, v_i_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
case 3:
{
lean_object* v_i_1672_; lean_object* v___x_1673_; 
v_i_1672_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1672_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1673_ = l_Lean_Elab_CommandInfo_format(v_ctx_1656_, v_i_1672_);
return v___x_1673_;
}
case 4:
{
lean_object* v_i_1674_; lean_object* v___x_1675_; 
v_i_1674_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1674_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1675_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1656_, v_i_1674_);
lean_dec_ref(v_ctx_1656_);
return v___x_1675_;
}
case 5:
{
lean_object* v_i_1676_; lean_object* v___x_1677_; 
v_i_1676_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1676_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1677_ = l_Lean_Elab_OptionInfo_format(v_ctx_1656_, v_i_1676_);
return v___x_1677_;
}
case 6:
{
lean_object* v_i_1678_; lean_object* v___x_1679_; 
v_i_1678_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1678_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1679_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1656_, v_i_1678_);
return v___x_1679_;
}
case 7:
{
lean_object* v_i_1680_; lean_object* v___x_1681_; 
v_i_1680_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1680_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1681_ = l_Lean_Elab_FieldInfo_format(v_ctx_1656_, v_i_1680_);
return v___x_1681_;
}
case 8:
{
lean_object* v_i_1682_; lean_object* v___x_1683_; 
v_i_1682_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1682_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1683_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1656_, v_i_1682_);
return v___x_1683_;
}
case 9:
{
lean_object* v_i_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_ctx_1656_);
v_i_1684_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v_x_1657_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_i_1684_);
lean_dec(v_x_1657_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
case 10:
{
lean_object* v_i_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_ctx_1656_);
v_i_1693_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_x_1657_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_i_1693_);
lean_dec(v_x_1657_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = l_Lean_Elab_CustomInfo_format(v_i_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
case 11:
{
lean_object* v_i_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_ctx_1656_);
v_i_1702_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v_x_1657_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_i_1702_);
lean_dec(v_x_1657_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
case 12:
{
lean_object* v_i_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_i_1711_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v_x_1657_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_i_1711_);
lean_dec(v_x_1657_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1656_, v_i_1711_);
lean_dec(v_i_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
case 13:
{
lean_object* v_i_1720_; lean_object* v___x_1721_; 
v_i_1720_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_i_1720_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1721_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1656_, v_i_1720_);
return v___x_1721_;
}
case 14:
{
lean_object* v_i_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
v_i_1722_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_x_1657_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_i_1722_);
lean_dec(v_x_1657_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1656_, v_i_1722_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
case 15:
{
lean_object* v_i_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_i_1731_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v_x_1657_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_i_1731_);
lean_dec(v_x_1657_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1656_, v_i_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
case 16:
{
lean_object* v_i_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_i_1740_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v_x_1657_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_i_1740_);
lean_dec(v_x_1657_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = l_Lean_Elab_DocInfo_format(v_ctx_1656_, v_i_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
default: 
{
lean_object* v_i_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
v_i_1749_ = lean_ctor_get(v_x_1657_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_x_1657_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v_x_1657_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_i_1749_);
lean_dec(v_x_1657_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1656_, v_i_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1758_, lean_object* v_x_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Elab_Info_format(v_ctx_1758_, v_x_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
return v_x_1762_;
}
else
{
lean_object* v_head_1764_; lean_object* v_tail_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_head_1764_ = lean_ctor_get(v_x_1763_, 0);
v_tail_1765_ = lean_ctor_get(v_x_1763_, 1);
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1767_ = lean_string_append(v_x_1762_, v___x_1766_);
v___x_1768_ = lean_expr_dbg_to_string(v_head_1764_);
v___x_1769_ = lean_string_append(v___x_1767_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v_x_1762_ = v___x_1769_;
v_x_1763_ = v_tail_1765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1771_, v_x_1772_);
lean_dec(v_x_1772_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1777_;
}
else
{
lean_object* v_tail_1778_; 
v_tail_1778_ = lean_ctor_get(v_x_1776_, 1);
if (lean_obj_tag(v_tail_1778_) == 0)
{
lean_object* v_head_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_head_1779_ = lean_ctor_get(v_x_1776_, 0);
v___x_1780_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1781_ = lean_expr_dbg_to_string(v_head_1779_);
v___x_1782_ = lean_string_append(v___x_1780_, v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1784_ = lean_string_append(v___x_1782_, v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v_head_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint32_t v___x_1790_; lean_object* v___x_1791_; 
v_head_1785_ = lean_ctor_get(v_x_1776_, 0);
v___x_1786_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1787_ = lean_expr_dbg_to_string(v_head_1785_);
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1788_, v_tail_1778_);
v___x_1790_ = 93;
v___x_1791_ = lean_string_push(v___x_1789_, v___x_1790_);
return v___x_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1792_);
lean_dec(v_x_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1800_){
_start:
{
switch(lean_obj_tag(v_ctx_1800_))
{
case 0:
{
lean_object* v___x_1801_; 
lean_dec_ref_known(v_ctx_1800_, 1);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1801_;
}
case 1:
{
lean_object* v_parentDecl_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1815_; 
v_parentDecl_1802_ = lean_ctor_get(v_ctx_1800_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_ctx_1800_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1804_ = v_ctx_1800_;
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_parentDecl_1802_);
lean_dec(v_ctx_1800_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1807_ = 1;
v___x_1808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1802_, v___x_1807_);
v___x_1809_ = lean_string_append(v___x_1806_, v___x_1808_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 3);
lean_ctor_set(v___x_1804_, 0, v___x_1811_);
v___x_1813_ = v___x_1804_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1831_; 
v_autoImplicits_1816_ = lean_ctor_get(v_ctx_1800_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_ctx_1800_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1818_ = v_ctx_1800_;
v_isShared_1819_ = v_isSharedCheck_1831_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_autoImplicits_1816_);
lean_dec(v_ctx_1800_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1831_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1820_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1821_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1822_ = lean_array_to_list(v_autoImplicits_1816_);
v___x_1823_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1822_);
lean_dec(v___x_1822_);
v___x_1824_ = lean_string_append(v___x_1821_, v___x_1823_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = lean_string_append(v___x_1820_, v___x_1824_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1827_ = lean_string_append(v___x_1825_, v___x_1826_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 3);
lean_ctor_set(v___x_1818_, 0, v___x_1827_);
v___x_1829_ = v___x_1818_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1841_, lean_object* v_ctx_x3f_1842_){
_start:
{
switch(lean_obj_tag(v_tree_1841_))
{
case 0:
{
lean_object* v_i_1844_; lean_object* v_t_1845_; lean_object* v___x_1846_; 
v_i_1844_ = lean_ctor_get(v_tree_1841_, 0);
lean_inc_ref(v_i_1844_);
v_t_1845_ = lean_ctor_get(v_tree_1841_, 1);
lean_inc_ref(v_t_1845_);
lean_dec_ref_known(v_tree_1841_, 2);
v___x_1846_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1844_, v_ctx_x3f_1842_);
v_tree_1841_ = v_t_1845_;
v_ctx_x3f_1842_ = v___x_1846_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1842_) == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref_known(v_tree_1841_, 2);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
else
{
lean_object* v_i_1850_; lean_object* v_children_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1901_; 
v_i_1850_ = lean_ctor_get(v_tree_1841_, 0);
v_children_1851_ = lean_ctor_get(v_tree_1841_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_tree_1841_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1853_ = v_tree_1841_;
v_isShared_1854_ = v_isSharedCheck_1901_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_children_1851_);
lean_inc(v_i_1850_);
lean_dec(v_tree_1841_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1901_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_val_1855_; lean_object* v___x_1856_; 
v_val_1855_ = lean_ctor_get(v_ctx_x3f_1842_, 0);
lean_inc_ref(v_i_1850_);
lean_inc(v_val_1855_);
v___x_1856_ = l_Lean_Elab_Info_format(v_val_1855_, v_i_1850_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1900_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1900_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1900_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_size_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_size_1861_ = lean_ctor_get(v_children_1851_, 2);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_nat_dec_eq(v_size_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_del_object(v___x_1859_);
v___x_1864_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1842_, v_i_1850_);
lean_dec_ref(v_i_1850_);
v___x_1865_ = l_Lean_PersistentArray_toList___redArg(v_children_1851_);
lean_dec_ref(v_children_1851_);
v___x_1866_ = lean_box(0);
v___x_1867_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1864_, v___x_1865_, v___x_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1883_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1883_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1883_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 5);
lean_ctor_set(v___x_1853_, 1, v_a_1857_);
lean_ctor_set(v___x_1853_, 0, v___x_1872_);
v___x_1874_ = v___x_1853_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_a_1857_);
v___x_1874_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1875_ = lean_box(1);
v___x_1876_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1875_, v_a_1868_);
v___x_1877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1874_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Std_Format_nestD(v___x_1877_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1857_);
lean_del_object(v___x_1853_);
v_a_1884_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1867_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1867_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec_ref(v_children_1851_);
lean_dec_ref(v_i_1850_);
lean_dec_ref_known(v_ctx_x3f_1842_, 1);
v___x_1892_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 5);
lean_ctor_set(v___x_1853_, 1, v_a_1857_);
lean_ctor_set(v___x_1853_, 0, v___x_1892_);
v___x_1894_ = v___x_1853_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_a_1857_);
v___x_1894_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = l_Std_Format_nestD(v___x_1894_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1895_);
v___x_1897_ = v___x_1859_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_del_object(v___x_1853_);
lean_dec_ref(v_children_1851_);
lean_dec_ref(v_i_1850_);
lean_dec_ref_known(v_ctx_x3f_1842_, 1);
return v___x_1856_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_ctx_x3f_1842_);
v_mvarId_1902_ = lean_ctor_get(v_tree_1841_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_tree_1841_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1904_ = v_tree_1841_;
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_mvarId_1902_);
lean_dec(v_tree_1841_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1906_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1907_ = 1;
v___x_1908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1902_, v___x_1907_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 3);
lean_ctor_set(v___x_1904_, 0, v___x_1908_);
v___x_1910_ = v___x_1904_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Std_Format_nestD(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___x_1916_);
v___x_1920_ = l_List_reverse___redArg(v_x_1918_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v_head_1922_; lean_object* v_tail_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1941_; 
v_head_1922_ = lean_ctor_get(v_x_1917_, 0);
v_tail_1923_ = lean_ctor_get(v_x_1917_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1925_ = v_x_1917_;
v_isShared_1926_ = v_isSharedCheck_1941_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_tail_1923_);
lean_inc(v_head_1922_);
lean_dec(v_x_1917_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1941_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; 
lean_inc(v___x_1916_);
v___x_1927_ = l_Lean_Elab_InfoTree_format(v_head_1922_, v___x_1916_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v_x_1918_);
lean_ctor_set(v___x_1925_, 0, v_a_1928_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1928_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_x_1918_);
v___x_1930_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v_x_1917_ = v_tail_1923_;
v_x_1918_ = v___x_1930_;
goto _start;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_del_object(v___x_1925_);
lean_dec(v_tail_1923_);
lean_dec(v_x_1918_);
lean_dec(v___x_1916_);
v_a_1933_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1927_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1927_);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1942_, v_x_1943_, v_x_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1947_, lean_object* v_ctx_x3f_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Elab_InfoTree_format(v_tree_1947_, v_ctx_x3f_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1951_, lean_object* v_s_1952_){
_start:
{
uint8_t v_enabled_1953_; lean_object* v_assignment_1954_; lean_object* v_lazyAssignment_1955_; lean_object* v_trees_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_enabled_1953_ = lean_ctor_get_uint8(v_s_1952_, sizeof(void*)*3);
v_assignment_1954_ = lean_ctor_get(v_s_1952_, 0);
v_lazyAssignment_1955_ = lean_ctor_get(v_s_1952_, 1);
v_trees_1956_ = lean_ctor_get(v_s_1952_, 2);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_s_1952_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1958_ = v_s_1952_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_trees_1956_);
lean_inc(v_lazyAssignment_1955_);
lean_inc(v_assignment_1954_);
lean_dec(v_s_1952_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_apply_1(v_f_1951_, v_trees_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 2, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_assignment_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_lazyAssignment_1955_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v___x_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*3, v_enabled_1953_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1965_, lean_object* v_f_1966_){
_start:
{
lean_object* v_modifyInfoState_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; 
v_modifyInfoState_1967_ = lean_ctor_get(v_inst_1965_, 1);
lean_inc(v_modifyInfoState_1967_);
lean_dec_ref(v_inst_1965_);
v___f_1968_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1968_, 0, v_f_1966_);
v___x_1969_ = lean_apply_1(v_modifyInfoState_1967_, v___f_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_f_1972_){
_start:
{
lean_object* v_modifyInfoState_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; 
v_modifyInfoState_1973_ = lean_ctor_get(v_inst_1971_, 1);
lean_inc(v_modifyInfoState_1973_);
lean_dec_ref(v_inst_1971_);
v___f_1974_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1974_, 0, v_f_1972_);
v___x_1975_ = lean_apply_1(v_modifyInfoState_1973_, v___f_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = lean_unsigned_to_nat(32u);
v___x_1977_ = lean_mk_empty_array_with_capacity(v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1979_ = ((size_t)5ULL);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_unsigned_to_nat(32u);
v___x_1982_ = lean_mk_empty_array_with_capacity(v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1984_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1980_);
lean_ctor_set(v___x_1984_, 3, v___x_1980_);
lean_ctor_set_usize(v___x_1984_, 4, v___x_1979_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1985_){
_start:
{
uint8_t v_enabled_1986_; lean_object* v_assignment_1987_; lean_object* v_lazyAssignment_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_enabled_1986_ = lean_ctor_get_uint8(v_s_1985_, sizeof(void*)*3);
v_assignment_1987_ = lean_ctor_get(v_s_1985_, 0);
v_lazyAssignment_1988_ = lean_ctor_get(v_s_1985_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_s_1985_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v_s_1985_, 2);
lean_dec(v_unused_1997_);
v___x_1990_ = v_s_1985_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_lazyAssignment_1988_);
lean_inc(v_assignment_1987_);
lean_dec(v_s_1985_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 2, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_assignment_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_lazyAssignment_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v___x_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*3, v_enabled_1986_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1998_, lean_object* v_trees_1999_, lean_object* v_____r_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_apply_2(v_toPure_1998_, lean_box(0), v_trees_1999_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2002_, lean_object* v_modifyInfoState_2003_, lean_object* v___f_2004_, lean_object* v_toBind_2005_, lean_object* v_____do__lift_2006_){
_start:
{
lean_object* v_trees_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_trees_2007_ = lean_ctor_get(v_____do__lift_2006_, 2);
lean_inc_ref(v_trees_2007_);
lean_dec_ref(v_____do__lift_2006_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2008_, 0, v_toPure_2002_);
lean_closure_set(v___f_2008_, 1, v_trees_2007_);
v___x_2009_ = lean_apply_1(v_modifyInfoState_2003_, v___f_2004_);
v___x_2010_ = lean_apply_4(v_toBind_2005_, lean_box(0), lean_box(0), v___x_2009_, v___f_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2012_, lean_object* v_inst_2013_){
_start:
{
lean_object* v_toApplicative_2014_; lean_object* v_toBind_2015_; lean_object* v_getInfoState_2016_; lean_object* v_modifyInfoState_2017_; lean_object* v_toPure_2018_; lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; 
v_toApplicative_2014_ = lean_ctor_get(v_inst_2012_, 0);
lean_inc_ref(v_toApplicative_2014_);
v_toBind_2015_ = lean_ctor_get(v_inst_2012_, 1);
lean_inc_n(v_toBind_2015_, 2);
lean_dec_ref(v_inst_2012_);
v_getInfoState_2016_ = lean_ctor_get(v_inst_2013_, 0);
lean_inc(v_getInfoState_2016_);
v_modifyInfoState_2017_ = lean_ctor_get(v_inst_2013_, 1);
lean_inc(v_modifyInfoState_2017_);
lean_dec_ref(v_inst_2013_);
v_toPure_2018_ = lean_ctor_get(v_toApplicative_2014_, 1);
lean_inc(v_toPure_2018_);
lean_dec_ref(v_toApplicative_2014_);
v___f_2019_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2020_, 0, v_toPure_2018_);
lean_closure_set(v___f_2020_, 1, v_modifyInfoState_2017_);
lean_closure_set(v___f_2020_, 2, v___f_2019_);
lean_closure_set(v___f_2020_, 3, v_toBind_2015_);
v___x_2021_ = lean_apply_4(v_toBind_2015_, lean_box(0), lean_box(0), v_getInfoState_2016_, v___f_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2023_, v_inst_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2026_, lean_object* v_s_2027_){
_start:
{
uint8_t v_enabled_2028_; lean_object* v_assignment_2029_; lean_object* v_lazyAssignment_2030_; lean_object* v_trees_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2039_; 
v_enabled_2028_ = lean_ctor_get_uint8(v_s_2027_, sizeof(void*)*3);
v_assignment_2029_ = lean_ctor_get(v_s_2027_, 0);
v_lazyAssignment_2030_ = lean_ctor_get(v_s_2027_, 1);
v_trees_2031_ = lean_ctor_get(v_s_2027_, 2);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_s_2027_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2033_ = v_s_2027_;
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_trees_2031_);
lean_inc(v_lazyAssignment_2030_);
lean_inc(v_assignment_2029_);
lean_dec(v_s_2027_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = l_Lean_PersistentArray_push___redArg(v_trees_2031_, v_t_2026_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 2, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_assignment_2029_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_lazyAssignment_2030_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v___x_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2038_, sizeof(void*)*3, v_enabled_2028_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2040_, lean_object* v_modifyInfoState_2041_, lean_object* v___f_2042_, lean_object* v_____do__lift_2043_){
_start:
{
uint8_t v_enabled_2044_; 
v_enabled_2044_ = lean_ctor_get_uint8(v_____do__lift_2043_, sizeof(void*)*3);
if (v_enabled_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec_ref(v___f_2042_);
lean_dec(v_modifyInfoState_2041_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_apply_2(v_toPure_2040_, lean_box(0), v___x_2045_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; 
lean_dec(v_toPure_2040_);
v___x_2047_ = lean_apply_1(v_modifyInfoState_2041_, v___f_2042_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2048_, lean_object* v_modifyInfoState_2049_, lean_object* v___f_2050_, lean_object* v_____do__lift_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2048_, v_modifyInfoState_2049_, v___f_2050_, v_____do__lift_2051_);
lean_dec_ref(v_____do__lift_2051_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_t_2055_){
_start:
{
lean_object* v_toApplicative_2056_; lean_object* v_toBind_2057_; lean_object* v_getInfoState_2058_; lean_object* v_modifyInfoState_2059_; lean_object* v_toPure_2060_; lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___x_2063_; 
v_toApplicative_2056_ = lean_ctor_get(v_inst_2053_, 0);
lean_inc_ref(v_toApplicative_2056_);
v_toBind_2057_ = lean_ctor_get(v_inst_2053_, 1);
lean_inc(v_toBind_2057_);
lean_dec_ref(v_inst_2053_);
v_getInfoState_2058_ = lean_ctor_get(v_inst_2054_, 0);
lean_inc(v_getInfoState_2058_);
v_modifyInfoState_2059_ = lean_ctor_get(v_inst_2054_, 1);
lean_inc(v_modifyInfoState_2059_);
lean_dec_ref(v_inst_2054_);
v_toPure_2060_ = lean_ctor_get(v_toApplicative_2056_, 1);
lean_inc(v_toPure_2060_);
lean_dec_ref(v_toApplicative_2056_);
v___f_2061_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2061_, 0, v_t_2055_);
v___f_2062_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2062_, 0, v_toPure_2060_);
lean_closure_set(v___f_2062_, 1, v_modifyInfoState_2059_);
lean_closure_set(v___f_2062_, 2, v___f_2061_);
v___x_2063_ = lean_apply_4(v_toBind_2057_, lean_box(0), lean_box(0), v_getInfoState_2058_, v___f_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_t_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2065_, v_inst_2066_, v_t_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2069_, lean_object* v_t_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_____do__lift_2073_){
_start:
{
uint8_t v_enabled_2074_; 
v_enabled_2074_ = lean_ctor_get_uint8(v_____do__lift_2073_, sizeof(void*)*3);
if (v_enabled_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref(v_inst_2072_);
lean_dec_ref(v_inst_2071_);
lean_dec_ref(v_t_2070_);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_apply_2(v_toPure_2069_, lean_box(0), v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec(v_toPure_2069_);
v___x_2077_ = lean_unsigned_to_nat(32u);
v___x_2078_ = lean_mk_empty_array_with_capacity(v___x_2077_);
lean_dec_ref(v___x_2078_);
v___x_2079_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_t_2070_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2071_, v_inst_2072_, v___x_2080_);
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2082_, lean_object* v_t_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_____do__lift_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2082_, v_t_2083_, v_inst_2084_, v_inst_2085_, v_____do__lift_2086_);
lean_dec_ref(v_____do__lift_2086_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_t_2090_){
_start:
{
lean_object* v_toApplicative_2091_; lean_object* v_toBind_2092_; lean_object* v_getInfoState_2093_; lean_object* v_toPure_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; 
v_toApplicative_2091_ = lean_ctor_get(v_inst_2088_, 0);
v_toBind_2092_ = lean_ctor_get(v_inst_2088_, 1);
lean_inc(v_toBind_2092_);
v_getInfoState_2093_ = lean_ctor_get(v_inst_2089_, 0);
lean_inc(v_getInfoState_2093_);
v_toPure_2094_ = lean_ctor_get(v_toApplicative_2091_, 1);
lean_inc(v_toPure_2094_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2095_, 0, v_toPure_2094_);
lean_closure_set(v___f_2095_, 1, v_t_2090_);
lean_closure_set(v___f_2095_, 2, v_inst_2088_);
lean_closure_set(v___f_2095_, 3, v_inst_2089_);
v___x_2096_ = lean_apply_4(v_toBind_2092_, lean_box(0), lean_box(0), v_getInfoState_2093_, v___f_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_t_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2098_, v_inst_2099_, v_t_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_info_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_info_2104_);
v___x_2106_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2102_, v_inst_2103_, v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_info_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2108_, v_inst_2109_, v_info_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2112_, lean_object* v_expectedType_x3f_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_____do__lift_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_stx_2112_);
v___x_2119_ = l_Lean_LocalContext_empty;
v___x_2120_ = 0;
v___x_2121_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2121_, 0, v___x_2118_);
lean_ctor_set(v___x_2121_, 1, v___x_2119_);
lean_ctor_set(v___x_2121_, 2, v_expectedType_x3f_2113_);
lean_ctor_set(v___x_2121_, 3, v_____do__lift_2116_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*4, v___x_2120_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*4 + 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2114_, v_inst_2115_, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_stx_2128_, lean_object* v_n_2129_, lean_object* v_expectedType_x3f_2130_){
_start:
{
lean_object* v_toBind_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_toBind_2131_ = lean_ctor_get(v_inst_2124_, 1);
lean_inc(v_toBind_2131_);
lean_inc_ref(v_inst_2124_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2132_, 0, v_stx_2128_);
lean_closure_set(v___f_2132_, 1, v_expectedType_x3f_2130_);
lean_closure_set(v___f_2132_, 2, v_inst_2124_);
lean_closure_set(v___f_2132_, 3, v_inst_2125_);
v___x_2133_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2124_, v_inst_2126_, v_inst_2127_, v_n_2129_);
v___x_2134_ = lean_apply_4(v_toBind_2131_, lean_box(0), lean_box(0), v___x_2133_, v___f_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_stx_2140_, lean_object* v_n_2141_, lean_object* v_expectedType_x3f_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v_stx_2140_, v_n_2141_, v_expectedType_x3f_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v_infoState_2148_; uint8_t v_enabled_2149_; 
v___x_2147_ = lean_st_ref_get(v___y_2145_);
v_infoState_2148_ = lean_ctor_get(v___x_2147_, 8);
lean_inc_ref(v_infoState_2148_);
lean_dec(v___x_2147_);
v_enabled_2149_ = lean_ctor_get_uint8(v_infoState_2148_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2148_);
if (v_enabled_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_t_2144_);
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; lean_object* v_infoState_2153_; lean_object* v_env_2154_; lean_object* v_nextMacroScope_2155_; lean_object* v_ngen_2156_; lean_object* v_auxDeclNGen_2157_; lean_object* v_traceState_2158_; lean_object* v_cache_2159_; lean_object* v_recordedDeps_2160_; lean_object* v_messages_2161_; lean_object* v_snapshotTasks_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2184_; 
v___x_2152_ = lean_st_ref_take(v___y_2145_);
v_infoState_2153_ = lean_ctor_get(v___x_2152_, 8);
v_env_2154_ = lean_ctor_get(v___x_2152_, 0);
v_nextMacroScope_2155_ = lean_ctor_get(v___x_2152_, 1);
v_ngen_2156_ = lean_ctor_get(v___x_2152_, 2);
v_auxDeclNGen_2157_ = lean_ctor_get(v___x_2152_, 3);
v_traceState_2158_ = lean_ctor_get(v___x_2152_, 4);
v_cache_2159_ = lean_ctor_get(v___x_2152_, 5);
v_recordedDeps_2160_ = lean_ctor_get(v___x_2152_, 6);
v_messages_2161_ = lean_ctor_get(v___x_2152_, 7);
v_snapshotTasks_2162_ = lean_ctor_get(v___x_2152_, 9);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2164_ = v___x_2152_;
v_isShared_2165_ = v_isSharedCheck_2184_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snapshotTasks_2162_);
lean_inc(v_infoState_2153_);
lean_inc(v_messages_2161_);
lean_inc(v_recordedDeps_2160_);
lean_inc(v_cache_2159_);
lean_inc(v_traceState_2158_);
lean_inc(v_auxDeclNGen_2157_);
lean_inc(v_ngen_2156_);
lean_inc(v_nextMacroScope_2155_);
lean_inc(v_env_2154_);
lean_dec(v___x_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2184_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v_enabled_2166_; lean_object* v_assignment_2167_; lean_object* v_lazyAssignment_2168_; lean_object* v_trees_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2183_; 
v_enabled_2166_ = lean_ctor_get_uint8(v_infoState_2153_, sizeof(void*)*3);
v_assignment_2167_ = lean_ctor_get(v_infoState_2153_, 0);
v_lazyAssignment_2168_ = lean_ctor_get(v_infoState_2153_, 1);
v_trees_2169_ = lean_ctor_get(v_infoState_2153_, 2);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_infoState_2153_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2171_ = v_infoState_2153_;
v_isShared_2172_ = v_isSharedCheck_2183_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_trees_2169_);
lean_inc(v_lazyAssignment_2168_);
lean_inc(v_assignment_2167_);
lean_dec(v_infoState_2153_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2183_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Lean_PersistentArray_push___redArg(v_trees_2169_, v_t_2144_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 2, v___x_2174_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_assignment_2167_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_lazyAssignment_2168_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v___x_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2182_, sizeof(void*)*3, v_enabled_2166_);
v___x_2176_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2178_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 8, v___x_2176_);
v___x_2178_ = v___x_2164_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_env_2154_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_nextMacroScope_2155_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_ngen_2156_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_auxDeclNGen_2157_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_traceState_2158_);
lean_ctor_set(v_reuseFailAlloc_2181_, 5, v_cache_2159_);
lean_ctor_set(v_reuseFailAlloc_2181_, 6, v_recordedDeps_2160_);
lean_ctor_set(v_reuseFailAlloc_2181_, 7, v_messages_2161_);
lean_ctor_set(v_reuseFailAlloc_2181_, 8, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2181_, 9, v_snapshotTasks_2162_);
v___x_2178_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_st_ref_put(v___y_2145_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2173_);
return v___x_2180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2185_, v___y_2186_);
lean_dec(v___y_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; lean_object* v_infoState_2194_; uint8_t v_enabled_2195_; 
v___x_2193_ = lean_st_ref_get(v___y_2191_);
v_infoState_2194_ = lean_ctor_get(v___x_2193_, 8);
lean_inc_ref(v_infoState_2194_);
lean_dec(v___x_2193_);
v_enabled_2195_ = lean_ctor_get_uint8(v_infoState_2194_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2194_);
if (v_enabled_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_t_2189_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2198_ = lean_unsigned_to_nat(32u);
v___x_2199_ = lean_mk_empty_array_with_capacity(v___x_2198_);
lean_dec_ref(v___x_2199_);
v___x_2200_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_t_2189_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2201_, v___y_2191_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
lean_ctor_set(v___x_2212_, 3, v___x_2211_);
lean_ctor_set(v___x_2212_, 4, v___x_2210_);
lean_ctor_set(v___x_2212_, 5, v___x_2210_);
lean_ctor_set(v___x_2212_, 6, v___x_2210_);
lean_ctor_set(v___x_2212_, 7, v___x_2210_);
lean_ctor_set(v___x_2212_, 8, v___x_2210_);
lean_ctor_set(v___x_2212_, 9, v___x_2210_);
lean_ctor_set(v___x_2212_, 10, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_box(1);
v___x_2214_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2213_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2238_, lean_object* v_declHint_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_env_2244_; uint8_t v___x_2245_; 
v___x_2242_ = lean_box(0);
v___x_2243_ = lean_st_ref_get(v___y_2240_);
v_env_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc_ref(v_env_2244_);
lean_dec(v___x_2243_);
v___x_2245_ = l_Lean_Name_isAnonymous(v_declHint_2239_);
if (v___x_2245_ == 0)
{
uint8_t v_isExporting_2246_; 
v_isExporting_2246_ = lean_ctor_get_uint8(v_env_2244_, sizeof(void*)*13);
if (v_isExporting_2246_ == 0)
{
lean_object* v___x_2247_; 
lean_dec_ref(v_env_2244_);
lean_dec(v_declHint_2239_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_msg_2238_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
lean_inc_ref(v_env_2244_);
v___x_2248_ = l_Lean_Environment_setExporting(v_env_2244_, v___x_2245_);
lean_inc(v_declHint_2239_);
lean_inc_ref(v___x_2248_);
v___x_2249_ = l_Lean_Environment_contains(v___x_2248_, v_declHint_2239_, v_isExporting_2246_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref(v___x_2248_);
lean_dec_ref(v_env_2244_);
lean_dec(v_declHint_2239_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_msg_2238_);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_c_2256_; lean_object* v___x_2257_; 
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2253_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2248_);
v___x_2254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2248_);
lean_ctor_set(v___x_2254_, 1, v___x_2251_);
lean_ctor_set(v___x_2254_, 2, v___x_2252_);
lean_ctor_set(v___x_2254_, 3, v___x_2253_);
lean_inc(v_declHint_2239_);
v___x_2255_ = l_Lean_MessageData_ofConstName(v_declHint_2239_, v___x_2245_);
v_c_2256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2256_, 0, v___x_2254_);
lean_ctor_set(v_c_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2248_, v_declHint_2239_);
lean_dec_ref(v___x_2248_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec_ref(v_env_2244_);
lean_dec(v_declHint_2239_);
v___x_2258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v_c_2256_);
v___x_2260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_MessageData_note(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_msg_2238_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
else
{
lean_object* v_val_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2299_; 
v_val_2265_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2267_ = v___x_2257_;
v_isShared_2268_ = v_isSharedCheck_2299_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_val_2265_);
lean_dec(v___x_2257_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2299_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v_moduleNames_2270_; lean_object* v_mod_2271_; uint8_t v___x_2272_; 
v___x_2269_ = l_Lean_Environment_header(v_env_2244_);
lean_dec_ref(v_env_2244_);
v_moduleNames_2270_ = lean_ctor_get(v___x_2269_, 4);
lean_inc_ref(v_moduleNames_2270_);
lean_dec_ref(v___x_2269_);
v_mod_2271_ = lean_array_get(v___x_2242_, v_moduleNames_2270_, v_val_2265_);
lean_dec(v_val_2265_);
lean_dec_ref(v_moduleNames_2270_);
v___x_2272_ = l_Lean_isPrivateName(v_declHint_2239_);
lean_dec(v_declHint_2239_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v_c_2256_);
v___x_2275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_MessageData_ofName(v_mod_2271_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_MessageData_note(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_msg_2238_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2282_);
v___x_2284_ = v___x_2267_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_c_2256_);
v___x_2288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_ofName(v_mod_2271_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_MessageData_note(v___x_2293_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_msg_2238_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2295_);
v___x_2297_ = v___x_2267_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2300_; 
lean_dec_ref(v_env_2244_);
lean_dec(v_declHint_2239_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_msg_2238_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2301_, v_declHint_2302_, v___y_2303_);
lean_dec(v___y_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2321_; 
v___x_2311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2306_, v_declHint_2307_, v___y_2309_);
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2316_ = l_Lean_unknownIdentifierMessageTag;
v___x_2317_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_a_2312_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2317_);
v___x_2319_ = v___x_2314_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2322_, lean_object* v_declHint_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2322_, v_declHint_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v_toCold_2333_; lean_object* v_env_2334_; lean_object* v_options_2335_; uint8_t v___x_2336_; lean_object* v_env_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2332_ = lean_st_ref_get(v___y_2330_);
v_toCold_2333_ = lean_ctor_get(v___y_2329_, 0);
v_env_2334_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_env_2334_);
lean_dec(v___x_2332_);
v_options_2335_ = lean_ctor_get(v_toCold_2333_, 2);
v___x_2336_ = 0;
v_env_2337_ = l_Lean_Environment_setRecordingDeps(v_env_2334_, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2339_ = lean_unsigned_to_nat(32u);
v___x_2340_ = lean_mk_empty_array_with_capacity(v___x_2339_);
lean_dec_ref(v___x_2340_);
v___x_2341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2335_);
v___x_2342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2342_, 0, v_env_2337_);
lean_ctor_set(v___x_2342_, 1, v___x_2338_);
lean_ctor_set(v___x_2342_, 2, v___x_2341_);
lean_ctor_set(v___x_2342_, 3, v_options_2335_);
v___x_2343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_msgData_2328_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_ref_2354_; lean_object* v___x_2355_; lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_ref_2354_ = lean_ctor_get(v___y_2351_, 2);
v___x_2355_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2350_, v___y_2351_, v___y_2352_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_inc(v_ref_2354_);
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_ref_2354_);
lean_ctor_set(v___x_2360_, 1, v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 1);
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2370_, lean_object* v_msg_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_toCold_2375_; lean_object* v_currRecDepth_2376_; lean_object* v_ref_2377_; uint16_t v_optionFlags_2378_; uint8_t v_suppressElabErrors_2379_; uint8_t v_checkDeprecated_2380_; uint8_t v_isRecordingDeps_2381_; lean_object* v_ref_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_toCold_2375_ = lean_ctor_get(v___y_2372_, 0);
v_currRecDepth_2376_ = lean_ctor_get(v___y_2372_, 1);
v_ref_2377_ = lean_ctor_get(v___y_2372_, 2);
v_optionFlags_2378_ = lean_ctor_get_uint16(v___y_2372_, sizeof(void*)*3);
v_suppressElabErrors_2379_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*3 + 2);
v_checkDeprecated_2380_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2381_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*3 + 4);
v_ref_2382_ = l_Lean_replaceRef(v_ref_2370_, v_ref_2377_);
lean_inc(v_currRecDepth_2376_);
lean_inc_ref(v_toCold_2375_);
v___x_2383_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2383_, 0, v_toCold_2375_);
lean_ctor_set(v___x_2383_, 1, v_currRecDepth_2376_);
lean_ctor_set(v___x_2383_, 2, v_ref_2382_);
lean_ctor_set_uint16(v___x_2383_, sizeof(void*)*3, v_optionFlags_2378_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*3 + 2, v_suppressElabErrors_2379_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*3 + 3, v_checkDeprecated_2380_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*3 + 4, v_isRecordingDeps_2381_);
v___x_2384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2371_, v___x_2383_, v___y_2373_);
lean_dec_ref_known(v___x_2383_, 3);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2385_, lean_object* v_msg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2385_, v_msg_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_ref_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2391_, lean_object* v_msg_2392_, lean_object* v_declHint_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2399_; 
v___x_2397_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2392_, v_declHint_2393_, v___y_2394_, v___y_2395_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2391_, v_a_2398_, v___y_2394_, v___y_2395_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2400_, lean_object* v_msg_2401_, lean_object* v_declHint_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2400_, v_msg_2401_, v_declHint_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v_ref_2400_);
return v_res_2406_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2413_, lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2418_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2419_ = 0;
lean_inc(v_constName_2414_);
v___x_2420_ = l_Lean_MessageData_ofConstName(v_constName_2414_, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2418_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2413_, v___x_2423_, v_constName_2414_, v___y_2415_, v___y_2416_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2425_, lean_object* v_constName_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2425_, v_constName_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_ref_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; 
v_ref_2435_ = lean_ctor_get(v___y_2432_, 2);
v___x_2436_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2435_, v_constName_2431_, v___y_2432_, v___y_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v_env_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = lean_st_ref_get(v___y_2444_);
v_env_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc_ref(v_env_2447_);
lean_dec(v___x_2446_);
v___x_2448_ = 0;
lean_inc(v_constName_2442_);
v___x_2449_ = l_Lean_Environment_findConstVal_x3f(v_env_2447_, v_constName_2442_, v___x_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2442_, v___y_2443_, v___y_2444_);
return v___x_2450_;
}
else
{
lean_object* v_val_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_constName_2442_);
v_val_2451_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2449_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_val_2451_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 0);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_val_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
if (lean_obj_tag(v_a_2464_) == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = l_List_reverse___redArg(v_a_2465_);
return v___x_2466_;
}
else
{
lean_object* v_head_2467_; lean_object* v_tail_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2477_; 
v_head_2467_ = lean_ctor_get(v_a_2464_, 0);
v_tail_2468_ = lean_ctor_get(v_a_2464_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2470_ = v_a_2464_;
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_tail_2468_);
lean_inc(v_head_2467_);
lean_dec(v_a_2464_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = l_Lean_mkLevelParam(v_head_2467_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v_a_2465_);
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_a_2465_);
v___x_2474_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
v_a_2464_ = v_tail_2468_;
v_a_2465_ = v___x_2474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
lean_inc(v_constName_2478_);
v___x_2482_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2494_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_levelParams_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v_levelParams_2487_ = lean_ctor_get(v_a_2483_, 1);
lean_inc(v_levelParams_2487_);
lean_dec(v_a_2483_);
v___x_2488_ = lean_box(0);
v___x_2489_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2487_, v___x_2488_);
v___x_2490_ = l_Lean_mkConst(v_constName_2478_, v___x_2489_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2490_);
v___x_2492_ = v___x_2485_;
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
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_constName_2478_);
v_a_2495_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2482_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2482_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2508_, lean_object* v_n_2509_, lean_object* v_expectedType_x3f_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2509_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v_stx_2508_);
v___x_2518_ = l_Lean_LocalContext_empty;
v___x_2519_ = 0;
v___x_2520_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2520_, 0, v___x_2517_);
lean_ctor_set(v___x_2520_, 1, v___x_2518_);
lean_ctor_set(v___x_2520_, 2, v_expectedType_x3f_2510_);
lean_ctor_set(v___x_2520_, 3, v_a_2515_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*4, v___x_2519_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*4 + 1, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
v___x_2522_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2521_, v___y_2511_, v___y_2512_);
return v___x_2522_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_expectedType_x3f_2510_);
lean_dec(v_stx_2508_);
v_a_2523_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2514_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2514_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2531_, lean_object* v_n_2532_, lean_object* v_expectedType_x3f_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2531_, v_n_2532_, v_expectedType_x3f_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2538_, lean_object* v_expectedType_x3f_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; 
lean_inc(v_id_2538_);
v___x_2543_ = l_Lean_realizeGlobalConstNoOverload(v_id_2538_, v_a_2540_, v_a_2541_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2571_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2571_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2571_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v_infoState_2549_; uint8_t v_enabled_2550_; 
v___x_2548_ = lean_st_ref_get(v_a_2541_);
v_infoState_2549_ = lean_ctor_get(v___x_2548_, 8);
lean_inc_ref(v_infoState_2549_);
lean_dec(v___x_2548_);
v_enabled_2550_ = lean_ctor_get_uint8(v_infoState_2549_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2549_);
if (v_enabled_2550_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v_expectedType_x3f_2539_);
lean_dec(v_id_2538_);
if (v_isShared_2547_ == 0)
{
v___x_2552_ = v___x_2546_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2544_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
lean_object* v___x_2554_; 
lean_del_object(v___x_2546_);
lean_inc(v_a_2544_);
v___x_2554_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2538_, v_a_2544_, v_expectedType_x3f_2539_, v_a_2540_, v_a_2541_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2562_);
v___x_2556_ = v___x_2554_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v___x_2554_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_a_2544_);
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2544_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_a_2544_);
v_a_2563_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2554_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2554_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2539_);
lean_dec(v_id_2538_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2572_, lean_object* v_expectedType_x3f_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2572_, v_expectedType_x3f_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2578_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2588_, lean_object* v_constName_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2589_, v___y_2590_, v___y_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2594_, lean_object* v_constName_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2594_, v_constName_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2600_, lean_object* v_ref_2601_, lean_object* v_constName_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2601_, v_constName_2602_, v___y_2603_, v___y_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_ref_2608_, lean_object* v_constName_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2607_, v_ref_2608_, v_constName_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v_ref_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2614_, lean_object* v_ref_2615_, lean_object* v_msg_2616_, lean_object* v_declHint_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2615_, v_msg_2616_, v_declHint_2617_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_ref_2623_, lean_object* v_msg_2624_, lean_object* v_declHint_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2622_, v_ref_2623_, v_msg_2624_, v_declHint_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v_ref_2623_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2630_, lean_object* v_declHint_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2630_, v_declHint_2631_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2636_, lean_object* v_declHint_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2636_, v_declHint_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2642_, lean_object* v_ref_2643_, lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2643_, v_msg_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_ref_2650_, lean_object* v_msg_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2649_, v_ref_2650_, v_msg_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v_ref_2650_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2656_, lean_object* v_msg_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2657_, v___y_2658_, v___y_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_msg_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2662_, v_msg_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2668_, lean_object* v_expectedType_x3f_2669_, lean_object* v_as_x27_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
if (lean_obj_tag(v_as_x27_2670_) == 0)
{
lean_object* v___x_2675_; 
lean_dec(v_expectedType_x3f_2669_);
lean_dec(v_id_2668_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_b_2671_);
return v___x_2675_;
}
else
{
lean_object* v_head_2676_; lean_object* v_tail_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_head_2676_ = lean_ctor_get(v_as_x27_2670_, 0);
v_tail_2677_ = lean_ctor_get(v_as_x27_2670_, 1);
v___x_2678_ = lean_box(0);
lean_inc(v_expectedType_x3f_2669_);
lean_inc(v_head_2676_);
lean_inc(v_id_2668_);
v___x_2679_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2668_, v_head_2676_, v_expectedType_x3f_2669_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref_known(v___x_2679_, 1);
v_as_x27_2670_ = v_tail_2677_;
v_b_2671_ = v___x_2678_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2669_);
lean_dec(v_id_2668_);
return v___x_2679_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2681_, lean_object* v_expectedType_x3f_2682_, lean_object* v_as_x27_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2681_, v_expectedType_x3f_2682_, v_as_x27_2683_, v_b_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v_as_x27_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2689_, lean_object* v_expectedType_x3f_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; 
lean_inc(v_id_2689_);
v___x_2694_ = l_Lean_realizeGlobalConst(v_id_2689_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2723_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2723_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2723_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v_infoState_2700_; uint8_t v_enabled_2701_; 
v___x_2699_ = lean_st_ref_get(v_a_2692_);
v_infoState_2700_ = lean_ctor_get(v___x_2699_, 8);
lean_inc_ref(v_infoState_2700_);
lean_dec(v___x_2699_);
v_enabled_2701_ = lean_ctor_get_uint8(v_infoState_2700_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2700_);
if (v_enabled_2701_ == 0)
{
lean_object* v___x_2703_; 
lean_dec(v_expectedType_x3f_2690_);
lean_dec(v_id_2689_);
if (v_isShared_2698_ == 0)
{
v___x_2703_ = v___x_2697_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2695_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2697_);
v___x_2705_ = lean_box(0);
v___x_2706_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2689_, v_expectedType_x3f_2690_, v_a_2695_, v___x_2705_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; 
v_unused_2714_ = lean_ctor_get(v___x_2706_, 0);
lean_dec(v_unused_2714_);
v___x_2708_ = v___x_2706_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_dec(v___x_2706_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v_a_2695_);
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2695_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2695_);
v_a_2715_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2706_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2706_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
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
else
{
lean_dec(v_expectedType_x3f_2690_);
lean_dec(v_id_2689_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2724_, lean_object* v_expectedType_x3f_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2724_, v_expectedType_x3f_2725_, v_a_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2730_, lean_object* v_expectedType_x3f_2731_, lean_object* v_as_2732_, lean_object* v_as_x27_2733_, lean_object* v_b_2734_, lean_object* v_a_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2730_, v_expectedType_x3f_2731_, v_as_x27_2733_, v_b_2734_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2740_, lean_object* v_expectedType_x3f_2741_, lean_object* v_as_2742_, lean_object* v_as_x27_2743_, lean_object* v_b_2744_, lean_object* v_a_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2740_, v_expectedType_x3f_2741_, v_as_2742_, v_as_x27_2743_, v_b_2744_, v_a_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v_as_x27_2743_);
lean_dec(v_as_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2750_, lean_object* v_as_x27_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
if (lean_obj_tag(v_as_x27_2751_) == 0)
{
lean_object* v___x_2756_; 
lean_dec(v_ref_2750_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_b_2752_);
return v___x_2756_;
}
else
{
lean_object* v_head_2757_; lean_object* v_tail_2758_; lean_object* v_fst_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_head_2757_ = lean_ctor_get(v_as_x27_2751_, 0);
v_tail_2758_ = lean_ctor_get(v_as_x27_2751_, 1);
v_fst_2759_ = lean_ctor_get(v_head_2757_, 0);
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_box(0);
lean_inc(v_fst_2759_);
lean_inc(v_ref_2750_);
v___x_2762_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2750_, v_fst_2759_, v___x_2761_, v___y_2753_, v___y_2754_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_dec_ref_known(v___x_2762_, 1);
v_as_x27_2751_ = v_tail_2758_;
v_b_2752_ = v___x_2760_;
goto _start;
}
else
{
lean_dec(v_ref_2750_);
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2764_, lean_object* v_as_x27_2765_, lean_object* v_b_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2764_, v_as_x27_2765_, v_b_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v_as_x27_2765_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2771_, lean_object* v_id_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_realizeGlobalName(v_id_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2805_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2805_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2805_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v_infoState_2782_; uint8_t v_enabled_2783_; 
v___x_2781_ = lean_st_ref_get(v_a_2774_);
v_infoState_2782_ = lean_ctor_get(v___x_2781_, 8);
lean_inc_ref(v_infoState_2782_);
lean_dec(v___x_2781_);
v_enabled_2783_ = lean_ctor_get_uint8(v_infoState_2782_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2782_);
if (v_enabled_2783_ == 0)
{
lean_object* v___x_2785_; 
lean_dec(v_ref_2771_);
if (v_isShared_2780_ == 0)
{
v___x_2785_ = v___x_2779_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2777_);
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
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_del_object(v___x_2779_);
v___x_2787_ = lean_box(0);
v___x_2788_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2771_, v_a_2777_, v___x_2787_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2788_, 0);
lean_dec(v_unused_2796_);
v___x_2790_ = v___x_2788_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_a_2777_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2777_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_a_2777_);
v_a_2797_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2788_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2788_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2771_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2806_, lean_object* v_id_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2806_, v_id_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2812_, lean_object* v_as_2813_, lean_object* v_as_x27_2814_, lean_object* v_b_2815_, lean_object* v_a_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2812_, v_as_x27_2814_, v_b_2815_, v___y_2817_, v___y_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2821_, lean_object* v_as_2822_, lean_object* v_as_x27_2823_, lean_object* v_b_2824_, lean_object* v_a_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2821_, v_as_2822_, v_as_x27_2823_, v_b_2824_, v_a_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v_as_x27_2823_);
lean_dec(v_as_2822_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2830_){
_start:
{
lean_object* v_fst_2831_; 
v_fst_2831_ = lean_ctor_get(v_self_2830_, 0);
lean_inc(v_fst_2831_);
return v_fst_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2832_);
lean_dec_ref(v_self_2832_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2834_, lean_object* v_treesSaved_2835_, lean_object* v_s_2836_){
_start:
{
if (lean_obj_tag(v_info_2834_) == 0)
{
uint8_t v_enabled_2837_; lean_object* v_assignment_2838_; lean_object* v_lazyAssignment_2839_; lean_object* v_trees_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2850_; 
v_enabled_2837_ = lean_ctor_get_uint8(v_s_2836_, sizeof(void*)*3);
v_assignment_2838_ = lean_ctor_get(v_s_2836_, 0);
v_lazyAssignment_2839_ = lean_ctor_get(v_s_2836_, 1);
v_trees_2840_ = lean_ctor_get(v_s_2836_, 2);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_s_2836_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2842_ = v_s_2836_;
v_isShared_2843_ = v_isSharedCheck_2850_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_trees_2840_);
lean_inc(v_lazyAssignment_2839_);
lean_inc(v_assignment_2838_);
lean_dec(v_s_2836_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2850_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_val_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v_val_2844_ = lean_ctor_get(v_info_2834_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v_info_2834_, 1);
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_val_2844_);
lean_ctor_set(v___x_2845_, 1, v_trees_2840_);
v___x_2846_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2835_, v___x_2845_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 2, v___x_2846_);
v___x_2848_ = v___x_2842_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_assignment_2838_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_lazyAssignment_2839_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v___x_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*3, v_enabled_2837_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
uint8_t v_enabled_2851_; lean_object* v_assignment_2852_; lean_object* v_lazyAssignment_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2869_; 
v_enabled_2851_ = lean_ctor_get_uint8(v_s_2836_, sizeof(void*)*3);
v_assignment_2852_ = lean_ctor_get(v_s_2836_, 0);
v_lazyAssignment_2853_ = lean_ctor_get(v_s_2836_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_s_2836_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_s_2836_, 2);
lean_dec(v_unused_2870_);
v___x_2855_ = v_s_2836_;
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_lazyAssignment_2853_);
lean_inc(v_assignment_2852_);
lean_dec(v_s_2836_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_val_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2868_; 
v_val_2857_ = lean_ctor_get(v_info_2834_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_info_2834_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2859_ = v_info_2834_;
v_isShared_2860_ = v_isSharedCheck_2868_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_val_2857_);
lean_dec(v_info_2834_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2868_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 2);
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_val_2857_);
v___x_2862_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2835_, v___x_2862_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 2, v___x_2863_);
v___x_2865_ = v___x_2855_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_assignment_2852_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_lazyAssignment_2853_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v___x_2863_);
lean_ctor_set_uint8(v_reuseFailAlloc_2866_, sizeof(void*)*3, v_enabled_2851_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2871_, lean_object* v_modifyInfoState_2872_, lean_object* v_info_2873_){
_start:
{
lean_object* v___f_2874_; lean_object* v___x_2875_; 
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2874_, 0, v_info_2873_);
lean_closure_set(v___f_2874_, 1, v_treesSaved_2871_);
v___x_2875_ = lean_apply_1(v_modifyInfoState_2872_, v___f_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2876_, lean_object* v_info_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_apply_1(v___f_2876_, v_info_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2879_, lean_object* v_toBind_2880_, lean_object* v___f_2881_, lean_object* v_____do__lift_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_____do__lift_2882_);
v___x_2884_ = lean_apply_2(v_toPure_2879_, lean_box(0), v___x_2883_);
v___x_2885_ = lean_apply_4(v_toBind_2880_, lean_box(0), lean_box(0), v___x_2884_, v___f_2881_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2886_, lean_object* v_mkInfoOnError_2887_, lean_object* v___f_2888_, lean_object* v_mkInfo_2889_, lean_object* v___f_2890_, lean_object* v_a_x3f_2891_){
_start:
{
if (lean_obj_tag(v_a_x3f_2891_) == 0)
{
lean_object* v___x_2892_; 
lean_dec(v___f_2890_);
lean_dec(v_mkInfo_2889_);
v___x_2892_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v_mkInfoOnError_2887_, v___f_2888_);
return v___x_2892_;
}
else
{
lean_object* v_val_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec(v___f_2888_);
lean_dec(v_mkInfoOnError_2887_);
v_val_2893_ = lean_ctor_get(v_a_x3f_2891_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v_a_x3f_2891_, 1);
v___x_2894_ = lean_apply_1(v_mkInfo_2889_, v_val_2893_);
v___x_2895_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v___x_2894_, v___f_2890_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2896_, lean_object* v_modifyInfoState_2897_, lean_object* v_toPure_2898_, lean_object* v_toBind_2899_, lean_object* v_mkInfoOnError_2900_, lean_object* v_mkInfo_2901_, lean_object* v_inst_2902_, lean_object* v_x_2903_, lean_object* v___f_2904_, lean_object* v_treesSaved_2905_){
_start:
{
lean_object* v_map_2906_; lean_object* v___f_2907_; lean_object* v___f_2908_; lean_object* v___f_2909_; lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_map_2906_ = lean_ctor_get(v_toFunctor_2896_, 0);
lean_inc(v_map_2906_);
lean_dec_ref(v_toFunctor_2896_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2907_, 0, v_treesSaved_2905_);
lean_closure_set(v___f_2907_, 1, v_modifyInfoState_2897_);
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2908_, 0, v___f_2907_);
lean_inc_ref(v___f_2908_);
lean_inc(v_toBind_2899_);
v___f_2909_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2909_, 0, v_toPure_2898_);
lean_closure_set(v___f_2909_, 1, v_toBind_2899_);
lean_closure_set(v___f_2909_, 2, v___f_2908_);
v___f_2910_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2910_, 0, v_toBind_2899_);
lean_closure_set(v___f_2910_, 1, v_mkInfoOnError_2900_);
lean_closure_set(v___f_2910_, 2, v___f_2909_);
lean_closure_set(v___f_2910_, 3, v_mkInfo_2901_);
lean_closure_set(v___f_2910_, 4, v___f_2908_);
v___x_2911_ = lean_apply_4(v_inst_2902_, lean_box(0), lean_box(0), v_x_2903_, v___f_2910_);
v___x_2912_ = lean_apply_4(v_map_2906_, lean_box(0), lean_box(0), v___f_2904_, v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2913_, lean_object* v_inst_2914_, lean_object* v_inst_2915_, lean_object* v_toBind_2916_, lean_object* v___f_2917_, lean_object* v_____do__lift_2918_){
_start:
{
uint8_t v_enabled_2919_; 
v_enabled_2919_ = lean_ctor_get_uint8(v_____do__lift_2918_, sizeof(void*)*3);
if (v_enabled_2919_ == 0)
{
lean_dec(v___f_2917_);
lean_dec(v_toBind_2916_);
lean_dec_ref(v_inst_2915_);
lean_dec_ref(v_inst_2914_);
lean_inc(v_x_2913_);
return v_x_2913_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2914_, v_inst_2915_);
v___x_2921_ = lean_apply_4(v_toBind_2916_, lean_box(0), lean_box(0), v___x_2920_, v___f_2917_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_toBind_2925_, lean_object* v___f_2926_, lean_object* v_____do__lift_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2922_, v_inst_2923_, v_inst_2924_, v_toBind_2925_, v___f_2926_, v_____do__lift_2927_);
lean_dec_ref(v_____do__lift_2927_);
lean_dec(v_x_2922_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2930_, lean_object* v_inst_2931_, lean_object* v_inst_2932_, lean_object* v_x_2933_, lean_object* v_mkInfo_2934_, lean_object* v_mkInfoOnError_2935_){
_start:
{
lean_object* v_toApplicative_2936_; lean_object* v_toBind_2937_; lean_object* v_getInfoState_2938_; lean_object* v_modifyInfoState_2939_; lean_object* v_toFunctor_2940_; lean_object* v_toPure_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; 
v_toApplicative_2936_ = lean_ctor_get(v_inst_2930_, 0);
v_toBind_2937_ = lean_ctor_get(v_inst_2930_, 1);
lean_inc_n(v_toBind_2937_, 3);
v_getInfoState_2938_ = lean_ctor_get(v_inst_2931_, 0);
lean_inc(v_getInfoState_2938_);
v_modifyInfoState_2939_ = lean_ctor_get(v_inst_2931_, 1);
v_toFunctor_2940_ = lean_ctor_get(v_toApplicative_2936_, 0);
v_toPure_2941_ = lean_ctor_get(v_toApplicative_2936_, 1);
v___f_2942_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2933_);
lean_inc(v_toPure_2941_);
lean_inc(v_modifyInfoState_2939_);
lean_inc_ref(v_toFunctor_2940_);
v___f_2943_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2943_, 0, v_toFunctor_2940_);
lean_closure_set(v___f_2943_, 1, v_modifyInfoState_2939_);
lean_closure_set(v___f_2943_, 2, v_toPure_2941_);
lean_closure_set(v___f_2943_, 3, v_toBind_2937_);
lean_closure_set(v___f_2943_, 4, v_mkInfoOnError_2935_);
lean_closure_set(v___f_2943_, 5, v_mkInfo_2934_);
lean_closure_set(v___f_2943_, 6, v_inst_2932_);
lean_closure_set(v___f_2943_, 7, v_x_2933_);
lean_closure_set(v___f_2943_, 8, v___f_2942_);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2944_, 0, v_x_2933_);
lean_closure_set(v___f_2944_, 1, v_inst_2930_);
lean_closure_set(v___f_2944_, 2, v_inst_2931_);
lean_closure_set(v___f_2944_, 3, v_toBind_2937_);
lean_closure_set(v___f_2944_, 4, v___f_2943_);
v___x_2945_ = lean_apply_4(v_toBind_2937_, lean_box(0), lean_box(0), v_getInfoState_2938_, v___f_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_00_u03b1_2949_, lean_object* v_inst_2950_, lean_object* v_x_2951_, lean_object* v_mkInfo_2952_, lean_object* v_mkInfoOnError_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2947_, v_inst_2948_, v_inst_2950_, v_x_2951_, v_mkInfo_2952_, v_mkInfoOnError_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2955_, lean_object* v_tree_2956_, lean_object* v_s_2957_){
_start:
{
uint8_t v_enabled_2958_; lean_object* v_assignment_2959_; lean_object* v_lazyAssignment_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2968_; 
v_enabled_2958_ = lean_ctor_get_uint8(v_s_2957_, sizeof(void*)*3);
v_assignment_2959_ = lean_ctor_get(v_s_2957_, 0);
v_lazyAssignment_2960_ = lean_ctor_get(v_s_2957_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_s_2957_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v_s_2957_, 2);
lean_dec(v_unused_2969_);
v___x_2962_ = v_s_2957_;
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_lazyAssignment_2960_);
lean_inc(v_assignment_2959_);
lean_dec(v_s_2957_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2955_, v_tree_2956_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 2, v___x_2964_);
v___x_2966_ = v___x_2962_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_assignment_2959_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_lazyAssignment_2960_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___x_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*3, v_enabled_2958_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2970_, lean_object* v_modifyInfoState_2971_, lean_object* v_tree_2972_){
_start:
{
lean_object* v___f_2973_; lean_object* v___x_2974_; 
v___f_2973_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2973_, 0, v_treesSaved_2970_);
lean_closure_set(v___f_2973_, 1, v_tree_2972_);
v___x_2974_ = lean_apply_1(v_modifyInfoState_2971_, v___f_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2975_, lean_object* v_toBind_2976_, lean_object* v___f_2977_, lean_object* v_st_2978_){
_start:
{
lean_object* v_trees_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_trees_2979_ = lean_ctor_get(v_st_2978_, 2);
lean_inc_ref(v_trees_2979_);
lean_dec_ref(v_st_2978_);
v___x_2980_ = lean_apply_1(v_mkInfoTree_2975_, v_trees_2979_);
v___x_2981_ = lean_apply_4(v_toBind_2976_, lean_box(0), lean_box(0), v___x_2980_, v___f_2977_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2982_, lean_object* v_getInfoState_2983_, lean_object* v___f_2984_, lean_object* v_x_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_apply_4(v_toBind_2982_, lean_box(0), lean_box(0), v_getInfoState_2983_, v___f_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2987_, lean_object* v_getInfoState_2988_, lean_object* v___f_2989_, lean_object* v_x_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2987_, v_getInfoState_2988_, v___f_2989_, v_x_2990_);
lean_dec(v_x_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2992_, lean_object* v_modifyInfoState_2993_, lean_object* v_mkInfoTree_2994_, lean_object* v_toBind_2995_, lean_object* v_getInfoState_2996_, lean_object* v_inst_2997_, lean_object* v_x_2998_, lean_object* v___f_2999_, lean_object* v_treesSaved_3000_){
_start:
{
lean_object* v_map_3001_; lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_map_3001_ = lean_ctor_get(v_toFunctor_2992_, 0);
lean_inc(v_map_3001_);
lean_dec_ref(v_toFunctor_2992_);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3002_, 0, v_treesSaved_3000_);
lean_closure_set(v___f_3002_, 1, v_modifyInfoState_2993_);
lean_inc(v_toBind_2995_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3003_, 0, v_mkInfoTree_2994_);
lean_closure_set(v___f_3003_, 1, v_toBind_2995_);
lean_closure_set(v___f_3003_, 2, v___f_3002_);
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3004_, 0, v_toBind_2995_);
lean_closure_set(v___f_3004_, 1, v_getInfoState_2996_);
lean_closure_set(v___f_3004_, 2, v___f_3003_);
v___x_3005_ = lean_apply_4(v_inst_2997_, lean_box(0), lean_box(0), v_x_2998_, v___f_3004_);
v___x_3006_ = lean_apply_4(v_map_3001_, lean_box(0), lean_box(0), v___f_2999_, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_x_3010_, lean_object* v_mkInfoTree_3011_){
_start:
{
lean_object* v_toApplicative_3012_; lean_object* v_toBind_3013_; lean_object* v_getInfoState_3014_; lean_object* v_modifyInfoState_3015_; lean_object* v_toFunctor_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; 
v_toApplicative_3012_ = lean_ctor_get(v_inst_3007_, 0);
v_toBind_3013_ = lean_ctor_get(v_inst_3007_, 1);
lean_inc_n(v_toBind_3013_, 3);
v_getInfoState_3014_ = lean_ctor_get(v_inst_3008_, 0);
lean_inc_n(v_getInfoState_3014_, 2);
v_modifyInfoState_3015_ = lean_ctor_get(v_inst_3008_, 1);
v_toFunctor_3016_ = lean_ctor_get(v_toApplicative_3012_, 0);
v___f_3017_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3010_);
lean_inc(v_modifyInfoState_3015_);
lean_inc_ref(v_toFunctor_3016_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3018_, 0, v_toFunctor_3016_);
lean_closure_set(v___f_3018_, 1, v_modifyInfoState_3015_);
lean_closure_set(v___f_3018_, 2, v_mkInfoTree_3011_);
lean_closure_set(v___f_3018_, 3, v_toBind_3013_);
lean_closure_set(v___f_3018_, 4, v_getInfoState_3014_);
lean_closure_set(v___f_3018_, 5, v_inst_3009_);
lean_closure_set(v___f_3018_, 6, v_x_3010_);
lean_closure_set(v___f_3018_, 7, v___f_3017_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3019_, 0, v_x_3010_);
lean_closure_set(v___f_3019_, 1, v_inst_3007_);
lean_closure_set(v___f_3019_, 2, v_inst_3008_);
lean_closure_set(v___f_3019_, 3, v_toBind_3013_);
lean_closure_set(v___f_3019_, 4, v___f_3018_);
v___x_3020_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v_getInfoState_3014_, v___f_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_00_u03b1_3024_, lean_object* v_inst_3025_, lean_object* v_x_3026_, lean_object* v_mkInfoTree_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3022_, v_inst_3023_, v_inst_3025_, v_x_3026_, v_mkInfoTree_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3029_, lean_object* v_toPure_3030_, lean_object* v_____do__lift_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3032_, 0, v_____do__lift_3031_);
lean_ctor_set(v___x_3032_, 1, v_trees_3029_);
v___x_3033_ = lean_apply_2(v_toPure_3030_, lean_box(0), v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3034_, lean_object* v_toBind_3035_, lean_object* v_mkInfo_3036_, lean_object* v_trees_3037_){
_start:
{
lean_object* v___f_3038_; lean_object* v___x_3039_; 
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3038_, 0, v_trees_3037_);
lean_closure_set(v___f_3038_, 1, v_toPure_3034_);
v___x_3039_ = lean_apply_4(v_toBind_3035_, lean_box(0), lean_box(0), v_mkInfo_3036_, v___f_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_x_3043_, lean_object* v_mkInfo_3044_){
_start:
{
lean_object* v_toApplicative_3045_; lean_object* v_toBind_3046_; lean_object* v_toPure_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; 
v_toApplicative_3045_ = lean_ctor_get(v_inst_3040_, 0);
v_toBind_3046_ = lean_ctor_get(v_inst_3040_, 1);
v_toPure_3047_ = lean_ctor_get(v_toApplicative_3045_, 1);
lean_inc(v_toBind_3046_);
lean_inc(v_toPure_3047_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3048_, 0, v_toPure_3047_);
lean_closure_set(v___f_3048_, 1, v_toBind_3046_);
lean_closure_set(v___f_3048_, 2, v_mkInfo_3044_);
v___x_3049_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3040_, v_inst_3041_, v_inst_3042_, v_x_3043_, v___f_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_00_u03b1_3053_, lean_object* v_inst_3054_, lean_object* v_x_3055_, lean_object* v_mkInfo_3056_){
_start:
{
lean_object* v_toApplicative_3057_; lean_object* v_toBind_3058_; lean_object* v_toPure_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; 
v_toApplicative_3057_ = lean_ctor_get(v_inst_3051_, 0);
v_toBind_3058_ = lean_ctor_get(v_inst_3051_, 1);
v_toPure_3059_ = lean_ctor_get(v_toApplicative_3057_, 1);
lean_inc(v_toBind_3058_);
lean_inc(v_toPure_3059_);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3060_, 0, v_toPure_3059_);
lean_closure_set(v___f_3060_, 1, v_toBind_3058_);
lean_closure_set(v___f_3060_, 2, v_mkInfo_3056_);
v___x_3061_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3051_, v_inst_3052_, v_inst_3054_, v_x_3055_, v___f_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3062_, lean_object* v_trees_3063_, lean_object* v_s_3064_){
_start:
{
uint8_t v_enabled_3065_; lean_object* v_assignment_3066_; lean_object* v_lazyAssignment_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
v_enabled_3065_ = lean_ctor_get_uint8(v_s_3064_, sizeof(void*)*3);
v_assignment_3066_ = lean_ctor_get(v_s_3064_, 0);
v_lazyAssignment_3067_ = lean_ctor_get(v_s_3064_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_s_3064_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v_s_3064_, 2);
lean_dec(v_unused_3076_);
v___x_3069_ = v_s_3064_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_lazyAssignment_3067_);
lean_inc(v_assignment_3066_);
lean_dec(v_s_3064_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3062_, v_trees_3063_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 2, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_assignment_3066_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_lazyAssignment_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v___x_3071_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*3, v_enabled_3065_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3077_, lean_object* v_trees_3078_, lean_object* v_s_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3077_, v_trees_3078_, v_s_3079_);
lean_dec_ref(v_trees_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3081_, lean_object* v_modifyInfoState_3082_, lean_object* v_trees_3083_){
_start:
{
lean_object* v___f_3084_; lean_object* v___x_3085_; 
v___f_3084_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3084_, 0, v_treesSaved_3081_);
lean_closure_set(v___f_3084_, 1, v_trees_3083_);
v___x_3085_ = lean_apply_1(v_modifyInfoState_3082_, v___f_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3086_, lean_object* v_tree_3087_, lean_object* v_____do__lift_3088_){
_start:
{
if (lean_obj_tag(v_____do__lift_3088_) == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_apply_2(v_toPure_3086_, lean_box(0), v_tree_3087_);
return v___x_3089_;
}
else
{
lean_object* v_val_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_val_3090_ = lean_ctor_get(v_____do__lift_3088_, 0);
lean_inc(v_val_3090_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v_val_3090_);
lean_ctor_set(v___x_3091_, 1, v_tree_3087_);
v___x_3092_ = lean_apply_2(v_toPure_3086_, lean_box(0), v___x_3091_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3093_, lean_object* v_tree_3094_, lean_object* v_____do__lift_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3093_, v_tree_3094_, v_____do__lift_3095_);
lean_dec(v_____do__lift_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3097_, lean_object* v_toPure_3098_, lean_object* v_toBind_3099_, lean_object* v_ctx_x3f_3100_, lean_object* v_tree_3101_){
_start:
{
lean_object* v_tree_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; 
v_tree_3102_ = l_Lean_Elab_InfoTree_substitute(v_tree_3101_, v_assignment_3097_);
v___f_3103_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3103_, 0, v_toPure_3098_);
lean_closure_set(v___f_3103_, 1, v_tree_3102_);
v___x_3104_ = lean_apply_4(v_toBind_3099_, lean_box(0), lean_box(0), v_ctx_x3f_3100_, v___f_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3105_, lean_object* v_toPure_3106_, lean_object* v_toBind_3107_, lean_object* v_ctx_x3f_3108_, lean_object* v_tree_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3105_, v_toPure_3106_, v_toBind_3107_, v_ctx_x3f_3108_, v_tree_3109_);
lean_dec_ref(v_assignment_3105_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3111_, lean_object* v_toBind_3112_, lean_object* v_ctx_x3f_3113_, lean_object* v_inst_3114_, lean_object* v___f_3115_, lean_object* v_st_3116_){
_start:
{
lean_object* v_assignment_3117_; lean_object* v_trees_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_assignment_3117_ = lean_ctor_get(v_st_3116_, 0);
lean_inc_ref(v_assignment_3117_);
v_trees_3118_ = lean_ctor_get(v_st_3116_, 2);
lean_inc_ref(v_trees_3118_);
lean_dec_ref(v_st_3116_);
lean_inc(v_toBind_3112_);
v___f_3119_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3119_, 0, v_assignment_3117_);
lean_closure_set(v___f_3119_, 1, v_toPure_3111_);
lean_closure_set(v___f_3119_, 2, v_toBind_3112_);
lean_closure_set(v___f_3119_, 3, v_ctx_x3f_3113_);
v___x_3120_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3114_, v___f_3119_, v_trees_3118_);
v___x_3121_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3120_, v___f_3115_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3122_, lean_object* v_modifyInfoState_3123_, lean_object* v_toPure_3124_, lean_object* v_toBind_3125_, lean_object* v_ctx_x3f_3126_, lean_object* v_inst_3127_, lean_object* v_getInfoState_3128_, lean_object* v_inst_3129_, lean_object* v_x_3130_, lean_object* v___f_3131_, lean_object* v_treesSaved_3132_){
_start:
{
lean_object* v_map_3133_; lean_object* v___f_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_map_3133_ = lean_ctor_get(v_toFunctor_3122_, 0);
lean_inc(v_map_3133_);
lean_dec_ref(v_toFunctor_3122_);
v___f_3134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3134_, 0, v_treesSaved_3132_);
lean_closure_set(v___f_3134_, 1, v_modifyInfoState_3123_);
lean_inc(v_toBind_3125_);
v___f_3135_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3135_, 0, v_toPure_3124_);
lean_closure_set(v___f_3135_, 1, v_toBind_3125_);
lean_closure_set(v___f_3135_, 2, v_ctx_x3f_3126_);
lean_closure_set(v___f_3135_, 3, v_inst_3127_);
lean_closure_set(v___f_3135_, 4, v___f_3134_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3136_, 0, v_toBind_3125_);
lean_closure_set(v___f_3136_, 1, v_getInfoState_3128_);
lean_closure_set(v___f_3136_, 2, v___f_3135_);
v___x_3137_ = lean_apply_4(v_inst_3129_, lean_box(0), lean_box(0), v_x_3130_, v___f_3136_);
v___x_3138_ = lean_apply_4(v_map_3133_, lean_box(0), lean_box(0), v___f_3131_, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_x_3142_, lean_object* v_ctx_x3f_3143_){
_start:
{
lean_object* v_toApplicative_3144_; lean_object* v_toBind_3145_; lean_object* v_getInfoState_3146_; lean_object* v_modifyInfoState_3147_; lean_object* v_toFunctor_3148_; lean_object* v_toPure_3149_; lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; 
v_toApplicative_3144_ = lean_ctor_get(v_inst_3139_, 0);
v_toBind_3145_ = lean_ctor_get(v_inst_3139_, 1);
lean_inc_n(v_toBind_3145_, 3);
v_getInfoState_3146_ = lean_ctor_get(v_inst_3140_, 0);
lean_inc_n(v_getInfoState_3146_, 2);
v_modifyInfoState_3147_ = lean_ctor_get(v_inst_3140_, 1);
v_toFunctor_3148_ = lean_ctor_get(v_toApplicative_3144_, 0);
v_toPure_3149_ = lean_ctor_get(v_toApplicative_3144_, 1);
v___f_3150_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3142_);
lean_inc_ref(v_inst_3139_);
lean_inc(v_toPure_3149_);
lean_inc(v_modifyInfoState_3147_);
lean_inc_ref(v_toFunctor_3148_);
v___f_3151_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3151_, 0, v_toFunctor_3148_);
lean_closure_set(v___f_3151_, 1, v_modifyInfoState_3147_);
lean_closure_set(v___f_3151_, 2, v_toPure_3149_);
lean_closure_set(v___f_3151_, 3, v_toBind_3145_);
lean_closure_set(v___f_3151_, 4, v_ctx_x3f_3143_);
lean_closure_set(v___f_3151_, 5, v_inst_3139_);
lean_closure_set(v___f_3151_, 6, v_getInfoState_3146_);
lean_closure_set(v___f_3151_, 7, v_inst_3141_);
lean_closure_set(v___f_3151_, 8, v_x_3142_);
lean_closure_set(v___f_3151_, 9, v___f_3150_);
v___f_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3152_, 0, v_x_3142_);
lean_closure_set(v___f_3152_, 1, v_inst_3139_);
lean_closure_set(v___f_3152_, 2, v_inst_3140_);
lean_closure_set(v___f_3152_, 3, v_toBind_3145_);
lean_closure_set(v___f_3152_, 4, v___f_3151_);
v___x_3153_ = lean_apply_4(v_toBind_3145_, lean_box(0), lean_box(0), v_getInfoState_3146_, v___f_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_00_u03b1_3157_, lean_object* v_inst_3158_, lean_object* v_x_3159_, lean_object* v_ctx_x3f_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3155_, v_inst_3156_, v_inst_3158_, v_x_3159_, v_ctx_x3f_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3162_, lean_object* v_____do__lift_3163_){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_____do__lift_3163_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
v___x_3166_ = lean_apply_2(v_toPure_3162_, lean_box(0), v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v_toPure_3179_; lean_object* v___x_3180_; lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3167_, 0);
v_toBind_3178_ = lean_ctor_get(v_inst_3167_, 1);
v_toPure_3179_ = lean_ctor_get(v_toApplicative_3177_, 1);
lean_inc_ref(v_inst_3167_);
v___x_3180_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3167_, v_inst_3171_, v_inst_3173_, v_inst_3172_, v_inst_3174_, v_inst_3169_, v_inst_3175_);
lean_inc(v_toPure_3179_);
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3181_, 0, v_toPure_3179_);
lean_inc(v_toBind_3178_);
v___x_3182_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v___x_3180_, v___f_3181_);
v___x_3183_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3167_, v_inst_3168_, v_inst_3170_, v_x_3176_, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_00_u03b1_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3185_, v_inst_3186_, v_inst_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_inst_3193_, v_inst_3194_, v_x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3197_, lean_object* v_____x_3198_){
_start:
{
if (lean_obj_tag(v_____x_3198_) == 1)
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3208_; 
v_val_3199_ = lean_ctor_get(v_____x_3198_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_____x_3198_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3201_ = v_____x_3198_;
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v_____x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_val_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_apply_2(v_toPure_3197_, lean_box(0), v___x_3205_);
return v___x_3206_;
}
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v_____x_3198_);
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_apply_2(v_toPure_3197_, lean_box(0), v___x_3209_);
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v_toApplicative_3216_; lean_object* v_toBind_3217_; lean_object* v_toPure_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_toApplicative_3216_ = lean_ctor_get(v_inst_3211_, 0);
v_toBind_3217_ = lean_ctor_get(v_inst_3211_, 1);
v_toPure_3218_ = lean_ctor_get(v_toApplicative_3216_, 1);
lean_inc(v_toPure_3218_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3219_, 0, v_toPure_3218_);
lean_inc(v_toBind_3217_);
v___x_3220_ = lean_apply_4(v_toBind_3217_, lean_box(0), lean_box(0), v_inst_3214_, v___f_3219_);
v___x_3221_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3211_, v_inst_3212_, v_inst_3213_, v_x_3215_, v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_00_u03b1_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_x_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3223_, v_inst_3224_, v_inst_3226_, v_inst_3227_, v_x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3230_, lean_object* v_autoImplicits_3231_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3232_, 0, v_autoImplicits_3231_);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
v___x_3234_ = lean_apply_2(v_toPure_3230_, lean_box(0), v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v_toApplicative_3240_; lean_object* v_toBind_3241_; lean_object* v_toPure_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_toApplicative_3240_ = lean_ctor_get(v_inst_3235_, 0);
v_toBind_3241_ = lean_ctor_get(v_inst_3235_, 1);
v_toPure_3242_ = lean_ctor_get(v_toApplicative_3240_, 1);
lean_inc(v_toPure_3242_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3243_, 0, v_toPure_3242_);
lean_inc(v_toBind_3241_);
v___x_3244_ = lean_apply_4(v_toBind_3241_, lean_box(0), lean_box(0), v_inst_3238_, v___f_3243_);
v___x_3245_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3235_, v_inst_3236_, v_inst_3237_, v_x_3239_, v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_00_u03b1_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3247_, v_inst_3248_, v_inst_3250_, v_inst_3251_, v_x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v_mvarId_3256_, lean_object* v_toPure_3257_, lean_object* v_____do__lift_3258_){
_start:
{
lean_object* v_assignment_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_assignment_3259_ = lean_ctor_get(v_____do__lift_3258_, 0);
v___x_3260_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3254_, v___x_3255_, v_assignment_3259_, v_mvarId_3256_);
v___x_3261_ = lean_apply_2(v_toPure_3257_, lean_box(0), v___x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_mvarId_3264_, lean_object* v_toPure_3265_, lean_object* v_____do__lift_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3262_, v___x_3263_, v_mvarId_3264_, v_toPure_3265_, v_____do__lift_3266_);
lean_dec_ref(v_____do__lift_3266_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_mvarId_3272_){
_start:
{
lean_object* v_toApplicative_3273_; lean_object* v_toBind_3274_; lean_object* v_getInfoState_3275_; lean_object* v_toPure_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v_toApplicative_3273_ = lean_ctor_get(v_inst_3270_, 0);
lean_inc_ref(v_toApplicative_3273_);
v_toBind_3274_ = lean_ctor_get(v_inst_3270_, 1);
lean_inc(v_toBind_3274_);
lean_dec_ref(v_inst_3270_);
v_getInfoState_3275_ = lean_ctor_get(v_inst_3271_, 0);
lean_inc(v_getInfoState_3275_);
lean_dec_ref(v_inst_3271_);
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3273_, 1);
lean_inc(v_toPure_3276_);
lean_dec_ref(v_toApplicative_3273_);
v___x_3277_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3278_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3279_, 0, v___x_3277_);
lean_closure_set(v___f_3279_, 1, v___x_3278_);
lean_closure_set(v___f_3279_, 2, v_mvarId_3272_);
lean_closure_set(v___f_3279_, 3, v_toPure_3276_);
v___x_3280_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v_getInfoState_3275_, v___f_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3281_, lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_mvarId_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3282_, v_inst_3283_, v_mvarId_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v_mvarId_3288_, lean_object* v_infoTree_3289_, lean_object* v_s_3290_){
_start:
{
uint8_t v_enabled_3291_; lean_object* v_assignment_3292_; lean_object* v_lazyAssignment_3293_; lean_object* v_trees_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3302_; 
v_enabled_3291_ = lean_ctor_get_uint8(v_s_3290_, sizeof(void*)*3);
v_assignment_3292_ = lean_ctor_get(v_s_3290_, 0);
v_lazyAssignment_3293_ = lean_ctor_get(v_s_3290_, 1);
v_trees_3294_ = lean_ctor_get(v_s_3290_, 2);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_s_3290_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3296_ = v_s_3290_;
v_isShared_3297_ = v_isSharedCheck_3302_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_trees_3294_);
lean_inc(v_lazyAssignment_3293_);
lean_inc(v_assignment_3292_);
lean_dec(v_s_3290_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3302_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3286_, v___x_3287_, v_assignment_3292_, v_mvarId_3288_, v_infoTree_3289_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3298_);
v___x_3300_ = v___x_3296_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_lazyAssignment_3293_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_trees_3294_);
lean_ctor_set_uint8(v_reuseFailAlloc_3301_, sizeof(void*)*3, v_enabled_3291_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3306_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3307_ = lean_unsigned_to_nat(2u);
v___x_3308_ = lean_unsigned_to_nat(384u);
v___x_3309_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3310_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3311_ = l_mkPanicMessageWithDecl(v___x_3310_, v___x_3309_, v___x_3308_, v___x_3307_, v___x_3306_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3312_, lean_object* v___f_3313_, lean_object* v___x_3314_, lean_object* v_____do__lift_3315_){
_start:
{
if (lean_obj_tag(v_____do__lift_3315_) == 0)
{
lean_object* v_modifyInfoState_3316_; lean_object* v___x_3317_; 
v_modifyInfoState_3316_ = lean_ctor_get(v_inst_3312_, 1);
lean_inc(v_modifyInfoState_3316_);
lean_dec_ref(v_inst_3312_);
v___x_3317_ = lean_apply_1(v_modifyInfoState_3316_, v___f_3313_);
return v___x_3317_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v___f_3313_);
lean_dec_ref(v_inst_3312_);
v___x_3318_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3319_ = l_panic___redArg(v___x_3314_, v___x_3318_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3320_, lean_object* v___f_3321_, lean_object* v___x_3322_, lean_object* v_____do__lift_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3320_, v___f_3321_, v___x_3322_, v_____do__lift_3323_);
lean_dec(v_____do__lift_3323_);
lean_dec(v___x_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_mvarId_3327_, lean_object* v_infoTree_3328_){
_start:
{
lean_object* v_toBind_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; 
v_toBind_3329_ = lean_ctor_get(v_inst_3325_, 1);
lean_inc(v_toBind_3329_);
v___x_3330_ = lean_box(0);
v___x_3331_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3332_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3327_);
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3333_, 0, v___x_3331_);
lean_closure_set(v___f_3333_, 1, v___x_3332_);
lean_closure_set(v___f_3333_, 2, v_mvarId_3327_);
lean_closure_set(v___f_3333_, 3, v_infoTree_3328_);
lean_inc_ref(v_inst_3326_);
lean_inc_ref(v_inst_3325_);
v___x_3334_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3325_, v_inst_3326_, v_mvarId_3327_);
v___x_3335_ = l_instInhabitedOfMonad___redArg(v_inst_3325_, v___x_3330_);
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3336_, 0, v_inst_3326_);
lean_closure_set(v___f_3336_, 1, v___f_3333_);
lean_closure_set(v___f_3336_, 2, v___x_3335_);
v___x_3337_ = lean_apply_4(v_toBind_3329_, lean_box(0), lean_box(0), v___x_3334_, v___f_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_mvarId_3341_, lean_object* v_infoTree_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3339_, v_inst_3340_, v_mvarId_3341_, v_infoTree_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3344_, lean_object* v_output_3345_, lean_object* v_toPure_3346_, lean_object* v_____do__lift_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3348_, 0, v_____do__lift_3347_);
lean_ctor_set(v___x_3348_, 1, v_stx_3344_);
lean_ctor_set(v___x_3348_, 2, v_output_3345_);
v___x_3349_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
v___x_3350_ = lean_apply_2(v_toPure_3346_, lean_box(0), v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_stx_3355_, lean_object* v_output_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v_toApplicative_3358_; lean_object* v_toBind_3359_; lean_object* v_toPure_3360_; lean_object* v___f_3361_; lean_object* v_mkInfo_3362_; lean_object* v___f_3363_; lean_object* v___x_3364_; 
v_toApplicative_3358_ = lean_ctor_get(v_inst_3352_, 0);
v_toBind_3359_ = lean_ctor_get(v_inst_3352_, 1);
v_toPure_3360_ = lean_ctor_get(v_toApplicative_3358_, 1);
lean_inc_n(v_toPure_3360_, 2);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3361_, 0, v_stx_3355_);
lean_closure_set(v___f_3361_, 1, v_output_3356_);
lean_closure_set(v___f_3361_, 2, v_toPure_3360_);
lean_inc_n(v_toBind_3359_, 2);
v_mkInfo_3362_ = lean_apply_4(v_toBind_3359_, lean_box(0), lean_box(0), v_inst_3354_, v___f_3361_);
v___f_3363_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3363_, 0, v_toPure_3360_);
lean_closure_set(v___f_3363_, 1, v_toBind_3359_);
lean_closure_set(v___f_3363_, 2, v_mkInfo_3362_);
v___x_3364_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3352_, v_inst_3353_, v_inst_3351_, v_x_3357_, v___f_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3365_, lean_object* v_00_u03b1_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_stx_3371_, lean_object* v_output_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3367_, v_inst_3368_, v_inst_3369_, v_inst_3370_, v_stx_3371_, v_output_3372_, v_x_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v___x_3378_, lean_object* v_mvarId_3379_, lean_object* v_s_3380_){
_start:
{
lean_object* v_trees_3381_; uint8_t v_enabled_3382_; lean_object* v_assignment_3383_; lean_object* v_lazyAssignment_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3401_; 
v_trees_3381_ = lean_ctor_get(v_s_3380_, 2);
v_enabled_3382_ = lean_ctor_get_uint8(v_s_3380_, sizeof(void*)*3);
v_assignment_3383_ = lean_ctor_get(v_s_3380_, 0);
v_lazyAssignment_3384_ = lean_ctor_get(v_s_3380_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_s_3380_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3386_ = v_s_3380_;
v_isShared_3387_ = v_isSharedCheck_3401_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_trees_3381_);
lean_inc(v_lazyAssignment_3384_);
lean_inc(v_assignment_3383_);
lean_dec(v_s_3380_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3401_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_size_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v_size_3388_ = lean_ctor_get(v_trees_3381_, 2);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_nat_dec_lt(v___x_3389_, v_size_3388_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v_trees_3381_);
lean_dec(v_mvarId_3379_);
lean_dec_ref(v___x_3378_);
lean_dec_ref(v___x_3377_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 2, v_treesSaved_3375_);
v___x_3392_ = v___x_3386_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_assignment_3383_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_lazyAssignment_3384_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_treesSaved_3375_);
lean_ctor_set_uint8(v_reuseFailAlloc_3393_, sizeof(void*)*3, v_enabled_3382_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3394_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_nat_sub(v_size_3388_, v___x_3394_);
v___x_3396_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3376_, v_trees_3381_, v___x_3395_);
lean_dec(v___x_3395_);
lean_dec_ref(v_trees_3381_);
v___x_3397_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3377_, v___x_3378_, v_assignment_3383_, v_mvarId_3379_, v___x_3396_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 2, v_treesSaved_3375_);
lean_ctor_set(v___x_3386_, 0, v___x_3397_);
v___x_3399_ = v___x_3386_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_lazyAssignment_3384_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_treesSaved_3375_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, sizeof(void*)*3, v_enabled_3382_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3402_, lean_object* v___x_3403_, lean_object* v___x_3404_, lean_object* v___x_3405_, lean_object* v_mvarId_3406_, lean_object* v_s_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3402_, v___x_3403_, v___x_3404_, v___x_3405_, v_mvarId_3406_, v_s_3407_);
lean_dec_ref(v___x_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3409_, lean_object* v___f_3410_, lean_object* v_x_3411_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_apply_1(v_modifyInfoState_3409_, v___f_3410_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3413_, lean_object* v___f_3414_, lean_object* v_x_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3413_, v___f_3414_, v_x_3415_);
lean_dec(v_x_3415_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v___x_3420_, lean_object* v_mvarId_3421_, lean_object* v_modifyInfoState_3422_, lean_object* v_inst_3423_, lean_object* v_x_3424_, lean_object* v___f_3425_, lean_object* v_treesSaved_3426_){
_start:
{
lean_object* v_map_3427_; lean_object* v___f_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_map_3427_ = lean_ctor_get(v_toFunctor_3417_, 0);
lean_inc(v_map_3427_);
lean_dec_ref(v_toFunctor_3417_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3428_, 0, v_treesSaved_3426_);
lean_closure_set(v___f_3428_, 1, v___x_3418_);
lean_closure_set(v___f_3428_, 2, v___x_3419_);
lean_closure_set(v___f_3428_, 3, v___x_3420_);
lean_closure_set(v___f_3428_, 4, v_mvarId_3421_);
v___f_3429_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3429_, 0, v_modifyInfoState_3422_);
lean_closure_set(v___f_3429_, 1, v___f_3428_);
v___x_3430_ = lean_apply_4(v_inst_3423_, lean_box(0), lean_box(0), v_x_3424_, v___f_3429_);
v___x_3431_ = lean_apply_4(v_map_3427_, lean_box(0), lean_box(0), v___f_3425_, v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_mvarId_3435_, lean_object* v_x_3436_){
_start:
{
lean_object* v_toApplicative_3437_; lean_object* v_toBind_3438_; lean_object* v_getInfoState_3439_; lean_object* v_modifyInfoState_3440_; lean_object* v_toFunctor_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___f_3446_; lean_object* v___f_3447_; lean_object* v___x_3448_; 
v_toApplicative_3437_ = lean_ctor_get(v_inst_3433_, 0);
v_toBind_3438_ = lean_ctor_get(v_inst_3433_, 1);
lean_inc_n(v_toBind_3438_, 2);
v_getInfoState_3439_ = lean_ctor_get(v_inst_3434_, 0);
lean_inc(v_getInfoState_3439_);
v_modifyInfoState_3440_ = lean_ctor_get(v_inst_3434_, 1);
v_toFunctor_3441_ = lean_ctor_get(v_toApplicative_3437_, 0);
v___f_3442_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3443_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3444_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3445_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3436_);
lean_inc(v_modifyInfoState_3440_);
lean_inc_ref(v_toFunctor_3441_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3446_, 0, v_toFunctor_3441_);
lean_closure_set(v___f_3446_, 1, v___x_3445_);
lean_closure_set(v___f_3446_, 2, v___x_3443_);
lean_closure_set(v___f_3446_, 3, v___x_3444_);
lean_closure_set(v___f_3446_, 4, v_mvarId_3435_);
lean_closure_set(v___f_3446_, 5, v_modifyInfoState_3440_);
lean_closure_set(v___f_3446_, 6, v_inst_3432_);
lean_closure_set(v___f_3446_, 7, v_x_3436_);
lean_closure_set(v___f_3446_, 8, v___f_3442_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3447_, 0, v_x_3436_);
lean_closure_set(v___f_3447_, 1, v_inst_3433_);
lean_closure_set(v___f_3447_, 2, v_inst_3434_);
lean_closure_set(v___f_3447_, 3, v_toBind_3438_);
lean_closure_set(v___f_3447_, 4, v___f_3446_);
v___x_3448_ = lean_apply_4(v_toBind_3438_, lean_box(0), lean_box(0), v_getInfoState_3439_, v___f_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3449_, lean_object* v_00_u03b1_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_mvarId_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v_toApplicative_3456_; lean_object* v_toBind_3457_; lean_object* v_getInfoState_3458_; lean_object* v_modifyInfoState_3459_; lean_object* v_toFunctor_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; 
v_toApplicative_3456_ = lean_ctor_get(v_inst_3452_, 0);
v_toBind_3457_ = lean_ctor_get(v_inst_3452_, 1);
lean_inc_n(v_toBind_3457_, 2);
v_getInfoState_3458_ = lean_ctor_get(v_inst_3453_, 0);
lean_inc(v_getInfoState_3458_);
v_modifyInfoState_3459_ = lean_ctor_get(v_inst_3453_, 1);
v_toFunctor_3460_ = lean_ctor_get(v_toApplicative_3456_, 0);
v___f_3461_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3462_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3463_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3464_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3455_);
lean_inc(v_modifyInfoState_3459_);
lean_inc_ref(v_toFunctor_3460_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3465_, 0, v_toFunctor_3460_);
lean_closure_set(v___f_3465_, 1, v___x_3464_);
lean_closure_set(v___f_3465_, 2, v___x_3462_);
lean_closure_set(v___f_3465_, 3, v___x_3463_);
lean_closure_set(v___f_3465_, 4, v_mvarId_3454_);
lean_closure_set(v___f_3465_, 5, v_modifyInfoState_3459_);
lean_closure_set(v___f_3465_, 6, v_inst_3451_);
lean_closure_set(v___f_3465_, 7, v_x_3455_);
lean_closure_set(v___f_3465_, 8, v___f_3461_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3466_, 0, v_x_3455_);
lean_closure_set(v___f_3466_, 1, v_inst_3452_);
lean_closure_set(v___f_3466_, 2, v_inst_3453_);
lean_closure_set(v___f_3466_, 3, v_toBind_3457_);
lean_closure_set(v___f_3466_, 4, v___f_3465_);
v___x_3467_ = lean_apply_4(v_toBind_3457_, lean_box(0), lean_box(0), v_getInfoState_3458_, v___f_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3468_, lean_object* v_s_3469_){
_start:
{
lean_object* v_assignment_3470_; lean_object* v_lazyAssignment_3471_; lean_object* v_trees_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
v_assignment_3470_ = lean_ctor_get(v_s_3469_, 0);
v_lazyAssignment_3471_ = lean_ctor_get(v_s_3469_, 1);
v_trees_3472_ = lean_ctor_get(v_s_3469_, 2);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_s_3469_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v_s_3469_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_trees_3472_);
lean_inc(v_lazyAssignment_3471_);
lean_inc(v_assignment_3470_);
lean_dec(v_s_3469_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_assignment_3470_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_lazyAssignment_3471_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_trees_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*3, v_flag_3468_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3480_, lean_object* v_s_3481_){
_start:
{
uint8_t v_flag_boxed_3482_; lean_object* v_res_3483_; 
v_flag_boxed_3482_ = lean_unbox(v_flag_3480_);
v_res_3483_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3482_, v_s_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3484_, uint8_t v_flag_3485_){
_start:
{
lean_object* v_modifyInfoState_3486_; lean_object* v___x_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; 
v_modifyInfoState_3486_ = lean_ctor_get(v_inst_3484_, 1);
lean_inc(v_modifyInfoState_3486_);
lean_dec_ref(v_inst_3484_);
v___x_3487_ = lean_box(v_flag_3485_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3488_, 0, v___x_3487_);
v___x_3489_ = lean_apply_1(v_modifyInfoState_3486_, v___f_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3490_, lean_object* v_flag_3491_){
_start:
{
uint8_t v_flag_boxed_3492_; lean_object* v_res_3493_; 
v_flag_boxed_3492_ = lean_unbox(v_flag_3491_);
v_res_3493_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3490_, v_flag_boxed_3492_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3494_, lean_object* v_inst_3495_, uint8_t v_flag_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3495_, v_flag_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3498_, lean_object* v_inst_3499_, lean_object* v_flag_3500_){
_start:
{
uint8_t v_flag_boxed_3501_; lean_object* v_res_3502_; 
v_flag_boxed_3501_ = lean_unbox(v_flag_3500_);
v_res_3502_ = l_Lean_Elab_enableInfoTree(v_m_3498_, v_inst_3499_, v_flag_boxed_3501_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3503_){
_start:
{
lean_object* v_fst_3504_; 
v_fst_3504_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_fst_3504_);
return v_fst_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3505_);
lean_dec_ref(v_x_3505_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3507_, lean_object* v_____r_3508_){
_start:
{
lean_inc(v_x_3507_);
return v_x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3509_, lean_object* v_____r_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3509_, v_____r_3510_);
lean_dec(v_x_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3512_, lean_object* v_x_3513_){
_start:
{
lean_inc(v___x_3512_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3514_, lean_object* v_x_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3514_, v_x_3515_);
lean_dec(v_x_3515_);
lean_dec(v___x_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3517_, lean_object* v_inst_3518_, uint8_t v_flag_3519_, lean_object* v_toBind_3520_, lean_object* v___f_3521_, lean_object* v_inst_3522_, lean_object* v___f_3523_, lean_object* v_____do__lift_3524_){
_start:
{
uint8_t v_enabled_3525_; lean_object* v_map_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___f_3530_; lean_object* v_y_3531_; lean_object* v___x_3532_; 
v_enabled_3525_ = lean_ctor_get_uint8(v_____do__lift_3524_, sizeof(void*)*3);
v_map_3526_ = lean_ctor_get(v_toFunctor_3517_, 0);
lean_inc(v_map_3526_);
lean_dec_ref(v_toFunctor_3517_);
lean_inc_ref(v_inst_3518_);
v___x_3527_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3518_, v_flag_3519_);
v___x_3528_ = lean_apply_4(v_toBind_3520_, lean_box(0), lean_box(0), v___x_3527_, v___f_3521_);
v___x_3529_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3518_, v_enabled_3525_);
v___f_3530_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3530_, 0, v___x_3529_);
v_y_3531_ = lean_apply_4(v_inst_3522_, lean_box(0), lean_box(0), v___x_3528_, v___f_3530_);
v___x_3532_ = lean_apply_4(v_map_3526_, lean_box(0), lean_box(0), v___f_3523_, v_y_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3533_, lean_object* v_inst_3534_, lean_object* v_flag_3535_, lean_object* v_toBind_3536_, lean_object* v___f_3537_, lean_object* v_inst_3538_, lean_object* v___f_3539_, lean_object* v_____do__lift_3540_){
_start:
{
uint8_t v_flag_boxed_3541_; lean_object* v_res_3542_; 
v_flag_boxed_3541_ = lean_unbox(v_flag_3535_);
v_res_3542_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3533_, v_inst_3534_, v_flag_boxed_3541_, v_toBind_3536_, v___f_3537_, v_inst_3538_, v___f_3539_, v_____do__lift_3540_);
lean_dec_ref(v_____do__lift_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, uint8_t v_flag_3547_, lean_object* v_x_3548_){
_start:
{
lean_object* v_toApplicative_3549_; lean_object* v_toBind_3550_; lean_object* v_getInfoState_3551_; lean_object* v_toFunctor_3552_; lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; lean_object* v___f_3556_; lean_object* v___x_3557_; 
v_toApplicative_3549_ = lean_ctor_get(v_inst_3544_, 0);
lean_inc_ref(v_toApplicative_3549_);
v_toBind_3550_ = lean_ctor_get(v_inst_3544_, 1);
lean_inc_n(v_toBind_3550_, 2);
lean_dec_ref(v_inst_3544_);
v_getInfoState_3551_ = lean_ctor_get(v_inst_3545_, 0);
lean_inc(v_getInfoState_3551_);
v_toFunctor_3552_ = lean_ctor_get(v_toApplicative_3549_, 0);
lean_inc_ref(v_toFunctor_3552_);
lean_dec_ref(v_toApplicative_3549_);
v___f_3553_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3554_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3554_, 0, v_x_3548_);
v___x_3555_ = lean_box(v_flag_3547_);
v___f_3556_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3556_, 0, v_toFunctor_3552_);
lean_closure_set(v___f_3556_, 1, v_inst_3545_);
lean_closure_set(v___f_3556_, 2, v___x_3555_);
lean_closure_set(v___f_3556_, 3, v_toBind_3550_);
lean_closure_set(v___f_3556_, 4, v___f_3554_);
lean_closure_set(v___f_3556_, 5, v_inst_3546_);
lean_closure_set(v___f_3556_, 6, v___f_3553_);
v___x_3557_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v_getInfoState_3551_, v___f_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3558_, lean_object* v_inst_3559_, lean_object* v_inst_3560_, lean_object* v_flag_3561_, lean_object* v_x_3562_){
_start:
{
uint8_t v_flag_boxed_3563_; lean_object* v_res_3564_; 
v_flag_boxed_3563_ = lean_unbox(v_flag_3561_);
v_res_3564_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3558_, v_inst_3559_, v_inst_3560_, v_flag_boxed_3563_, v_x_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3565_, lean_object* v_00_u03b1_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, uint8_t v_flag_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3567_, v_inst_3568_, v_inst_3569_, v_flag_3570_, v_x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3573_, lean_object* v_00_u03b1_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_flag_3578_, lean_object* v_x_3579_){
_start:
{
uint8_t v_flag_boxed_3580_; lean_object* v_res_3581_; 
v_flag_boxed_3580_ = lean_unbox(v_flag_3578_);
v_res_3581_ = l_Lean_Elab_withEnableInfoTree(v_m_3573_, v_00_u03b1_3574_, v_inst_3575_, v_inst_3576_, v_inst_3577_, v_flag_boxed_3580_, v_x_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3582_, lean_object* v_____do__lift_3583_){
_start:
{
lean_object* v_trees_3584_; lean_object* v___x_3585_; 
v_trees_3584_ = lean_ctor_get(v_____do__lift_3583_, 2);
lean_inc_ref(v_trees_3584_);
lean_dec_ref(v_____do__lift_3583_);
v___x_3585_ = lean_apply_2(v_toPure_3582_, lean_box(0), v_trees_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3586_, lean_object* v_inst_3587_){
_start:
{
lean_object* v_toApplicative_3588_; lean_object* v_toBind_3589_; lean_object* v_getInfoState_3590_; lean_object* v_toPure_3591_; lean_object* v___f_3592_; lean_object* v___x_3593_; 
v_toApplicative_3588_ = lean_ctor_get(v_inst_3587_, 0);
lean_inc_ref(v_toApplicative_3588_);
v_toBind_3589_ = lean_ctor_get(v_inst_3587_, 1);
lean_inc(v_toBind_3589_);
lean_dec_ref(v_inst_3587_);
v_getInfoState_3590_ = lean_ctor_get(v_inst_3586_, 0);
lean_inc(v_getInfoState_3590_);
lean_dec_ref(v_inst_3586_);
v_toPure_3591_ = lean_ctor_get(v_toApplicative_3588_, 1);
lean_inc(v_toPure_3591_);
lean_dec_ref(v_toApplicative_3588_);
v___f_3592_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3592_, 0, v_toPure_3591_);
v___x_3593_ = lean_apply_4(v_toBind_3589_, lean_box(0), lean_box(0), v_getInfoState_3590_, v___f_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3595_, v_inst_3596_);
return v___x_3597_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree_Basic(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Basic(builtin);
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
