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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
v___x_201_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v___x_198_);
lean_ctor_set(v___x_201_, 4, v___x_198_);
lean_ctor_set(v___x_201_, 5, v___x_198_);
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
v___x_337_ = lean_st_ref_take(v___y_334_);
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
v___x_353_ = lean_st_ref_put(v___y_334_, v___x_352_);
v___y_260_ = v___y_332_;
v___y_261_ = v___y_333_;
v___y_262_ = v___y_336_;
v___y_263_ = v___y_331_;
v___y_264_ = v___y_334_;
goto v___jp_259_;
}
}
}
v___jp_357_:
{
uint16_t v___x_362_; lean_object* v___x_363_; lean_object* v_env_364_; uint8_t v___x_365_; uint16_t v___x_366_; uint16_t v___x_367_; uint16_t v___x_368_; uint8_t v___x_369_; 
v___x_362_ = l_Lean_OptionFlags_ofOptions(v___y_361_);
v___x_363_ = lean_st_ref_get(v___y_360_);
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
v___y_332_ = v___y_359_;
v___y_333_ = v___y_361_;
v___y_334_ = v___y_360_;
v___y_335_ = v___x_254_;
v___y_336_ = v___x_362_;
goto v___jp_330_;
}
else
{
v___y_260_ = v___y_359_;
v___y_261_ = v___y_361_;
v___y_262_ = v___x_362_;
v___y_263_ = v___y_358_;
v___y_264_ = v___y_360_;
goto v___jp_259_;
}
}
else
{
if (v___x_365_ == 0)
{
v___y_260_ = v___y_359_;
v___y_261_ = v___y_361_;
v___y_262_ = v___x_362_;
v___y_263_ = v___y_358_;
v___y_264_ = v___y_360_;
goto v___jp_259_;
}
else
{
v___y_331_ = v___y_358_;
v___y_332_ = v___y_359_;
v___y_333_ = v___y_361_;
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
v___y_358_ = v___x_389_;
v___y_359_ = v___x_386_;
v___y_360_ = v___x_258_;
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
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_471_; uint64_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_474_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set_uint64(v___x_475_, sizeof(void*)*1, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_481_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
lean_ctor_set(v___x_481_, 4, v___x_480_);
lean_ctor_set(v___x_481_, 5, v___x_480_);
lean_ctor_set(v___x_481_, 6, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(32u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = ((size_t)5ULL);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_unsigned_to_nat(32u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_486_);
lean_ctor_set(v___x_490_, 3, v___x_486_);
lean_ctor_set_usize(v___x_490_, 4, v___x_485_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
lean_ctor_set(v___x_492_, 3, v___x_491_);
lean_ctor_set(v___x_492_, 4, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_493_, lean_object* v_lctx_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_toCommandContextInfo_505_; lean_object* v_mctx_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___x_512_; 
v___x_497_ = lean_box(1);
v___x_498_ = 0;
v___x_499_ = 1;
v___x_500_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_504_, 0, v___x_500_);
lean_ctor_set(v___x_504_, 1, v___x_497_);
lean_ctor_set(v___x_504_, 2, v_lctx_494_);
lean_ctor_set(v___x_504_, 3, v___x_502_);
lean_ctor_set(v___x_504_, 4, v___x_503_);
lean_ctor_set(v___x_504_, 5, v___x_501_);
lean_ctor_set(v___x_504_, 6, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*7, v___x_498_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*7 + 1, v___x_498_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*7 + 2, v___x_498_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*7 + 3, v___x_499_);
v_toCommandContextInfo_505_ = lean_ctor_get(v_info_493_, 0);
v_mctx_506_ = lean_ctor_get(v_toCommandContextInfo_505_, 3);
v___x_507_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_508_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_509_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
lean_inc_ref(v_mctx_506_);
v___x_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_510_, 0, v_mctx_506_);
lean_ctor_set(v___x_510_, 1, v___x_507_);
lean_ctor_set(v___x_510_, 2, v___x_497_);
lean_ctor_set(v___x_510_, 3, v___x_508_);
lean_ctor_set(v___x_510_, 4, v___x_509_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_511_, 0, v___x_510_);
lean_closure_set(v___f_511_, 1, v_x_495_);
lean_closure_set(v___f_511_, 2, v___x_504_);
v___x_512_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_493_, v___f_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_fst_517_; lean_object* v___x_519_; 
v_fst_517_ = lean_ctor_get(v_a_513_, 0);
lean_inc(v_fst_517_);
lean_dec(v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_fst_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_fst_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_512_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_512_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_530_, lean_object* v_lctx_531_, lean_object* v_x_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_530_, v_lctx_531_, v_x_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_535_, lean_object* v_info_536_, lean_object* v_lctx_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_536_, v_lctx_537_, v_x_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_541_, lean_object* v_info_542_, lean_object* v_lctx_543_, lean_object* v_x_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_541_, v_info_542_, v_lctx_543_, v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_547_, lean_object* v_lctx_548_){
_start:
{
lean_object* v_toCommandContextInfo_549_; lean_object* v_env_550_; lean_object* v_mctx_551_; lean_object* v_options_552_; lean_object* v_currNamespace_553_; lean_object* v_openDecls_554_; lean_object* v___x_555_; 
v_toCommandContextInfo_549_ = lean_ctor_get(v_info_547_, 0);
v_env_550_ = lean_ctor_get(v_toCommandContextInfo_549_, 0);
v_mctx_551_ = lean_ctor_get(v_toCommandContextInfo_549_, 3);
v_options_552_ = lean_ctor_get(v_toCommandContextInfo_549_, 4);
v_currNamespace_553_ = lean_ctor_get(v_toCommandContextInfo_549_, 5);
v_openDecls_554_ = lean_ctor_get(v_toCommandContextInfo_549_, 6);
lean_inc(v_openDecls_554_);
lean_inc(v_currNamespace_553_);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_mctx_551_);
lean_inc_ref(v_env_550_);
v___x_555_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_555_, 0, v_env_550_);
lean_ctor_set(v___x_555_, 1, v_mctx_551_);
lean_ctor_set(v___x_555_, 2, v_lctx_548_);
lean_ctor_set(v___x_555_, 3, v_options_552_);
lean_ctor_set(v___x_555_, 4, v_currNamespace_553_);
lean_ctor_set(v___x_555_, 5, v_openDecls_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_556_, lean_object* v_lctx_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_556_, v_lctx_557_);
lean_dec_ref(v_info_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_559_, lean_object* v_lctx_560_, lean_object* v_stx_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_559_, v_lctx_560_);
v___x_564_ = l_Lean_ppTerm(v___x_563_, v_stx_561_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_566_, lean_object* v_lctx_567_, lean_object* v_stx_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_566_, v_lctx_567_, v_stx_568_);
lean_dec_ref(v_info_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_586_, lean_object* v_pos_587_, lean_object* v_info_588_){
_start:
{
lean_object* v_toCommandContextInfo_589_; lean_object* v_fileMap_590_; lean_object* v___x_591_; lean_object* v_line_592_; lean_object* v_column_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_616_; 
v_toCommandContextInfo_589_ = lean_ctor_get(v_ctx_586_, 0);
lean_inc_ref(v_toCommandContextInfo_589_);
lean_dec_ref(v_ctx_586_);
v_fileMap_590_ = lean_ctor_get(v_toCommandContextInfo_589_, 2);
lean_inc_ref(v_fileMap_590_);
lean_dec_ref(v_toCommandContextInfo_589_);
v___x_591_ = l_Lean_FileMap_toPosition(v_fileMap_590_, v_pos_587_);
v_line_592_ = lean_ctor_get(v___x_591_, 0);
v_column_593_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_616_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_616_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_column_593_);
lean_inc(v_line_592_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_616_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_598_ = l_Nat_reprFast(v_line_592_);
v___x_599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 5);
lean_ctor_set(v___x_595_, 1, v___x_599_);
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_601_ = v___x_595_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_599_);
v___x_601_ = v_reuseFailAlloc_615_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_pos_608_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Nat_reprFast(v_column_593_);
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_608_, 0, v___x_606_);
lean_ctor_set(v_pos_608_, 1, v___x_607_);
switch(lean_obj_tag(v_info_588_))
{
case 0:
{
return v_pos_608_;
}
case 1:
{
uint8_t v_canonical_612_; 
v_canonical_612_ = lean_ctor_get_uint8(v_info_588_, sizeof(void*)*2);
if (v_canonical_612_ == 1)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v_pos_608_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
else
{
goto v___jp_609_;
}
}
default: 
{
goto v___jp_609_;
}
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v_pos_608_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_617_, lean_object* v_pos_618_, lean_object* v_info_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_617_, v_pos_618_, v_info_619_);
lean_dec(v_info_619_);
lean_dec(v_pos_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_624_, lean_object* v_stx_625_){
_start:
{
lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___x_636_; lean_object* v___y_638_; lean_object* v___x_641_; 
v___x_636_ = 0;
v___x_641_ = l_Lean_Syntax_getPos_x3f(v_stx_625_, v___x_636_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___y_638_ = v___x_642_;
goto v___jp_637_;
}
else
{
lean_object* v_val_643_; 
v_val_643_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v___x_641_, 1);
v___y_638_ = v_val_643_;
goto v___jp_637_;
}
v___jp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_629_ = l_Lean_Syntax_getHeadInfo(v_stx_625_);
lean_inc_ref(v_ctx_624_);
v___x_630_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_624_, v___y_627_, v___x_629_);
lean_dec(v___x_629_);
lean_dec(v___y_627_);
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_Syntax_getTailInfo(v_stx_625_);
v___x_634_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_624_, v___y_628_, v___x_633_);
lean_dec(v___x_633_);
lean_dec(v___y_628_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
v___jp_637_:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Syntax_getTailPos_x3f(v_stx_625_, v___x_636_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_inc(v___y_638_);
v___y_627_ = v___y_638_;
v___y_628_ = v___y_638_;
goto v___jp_626_;
}
else
{
lean_object* v_val_640_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v___y_627_ = v___y_638_;
v___y_628_ = v_val_640_;
goto v___jp_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_644_, lean_object* v_stx_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_644_, v_stx_645_);
lean_dec(v_stx_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_650_, lean_object* v_info_651_){
_start:
{
lean_object* v_elaborator_652_; lean_object* v_stx_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_668_; 
v_elaborator_652_ = lean_ctor_get(v_info_651_, 0);
v_stx_653_ = lean_ctor_get(v_info_651_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_info_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_655_ = v_info_651_;
v_isShared_656_ = v_isSharedCheck_668_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_stx_653_);
lean_inc(v_elaborator_652_);
lean_dec(v_info_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_668_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_Name_isAnonymous(v_elaborator_652_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_650_, v_stx_653_);
lean_dec(v_stx_653_);
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 5);
lean_ctor_set(v___x_655_, 1, v___x_659_);
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_666_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = 1;
v___x_663_ = l_Lean_Name_toString(v_elaborator_652_, v___x_662_);
v___x_664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_661_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
return v___x_665_;
}
}
else
{
lean_object* v___x_667_; 
lean_del_object(v___x_655_);
lean_dec(v_elaborator_652_);
v___x_667_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_650_, v_stx_653_);
lean_dec(v_stx_653_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_669_, lean_object* v_ctx_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_lctx_673_; lean_object* v___x_674_; 
v_lctx_673_ = lean_ctor_get(v_info_669_, 1);
lean_inc_ref(v_lctx_673_);
lean_dec_ref(v_info_669_);
v___x_674_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_670_, v_lctx_673_, v_x_671_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_675_, lean_object* v_ctx_676_, lean_object* v_x_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_675_, v_ctx_676_, v_x_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_680_, lean_object* v_info_681_, lean_object* v_ctx_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_681_, v_ctx_682_, v_x_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_686_, lean_object* v_info_687_, lean_object* v_ctx_688_, lean_object* v_x_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_686_, v_info_687_, v_ctx_688_, v_x_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_706_, lean_object* v_toElabInfo_707_, lean_object* v_expr_708_, uint8_t v_isBinder_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v_a_730_; lean_object* v___y_740_; lean_object* v_a_741_; lean_object* v___x_745_; 
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc_ref(v_expr_708_);
v___x_745_ = lean_infer_type(v_expr_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_Meta_ppExpr(v_a_746_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_a_730_ = v_a_748_;
goto v___jp_729_;
}
else
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_749_);
v___y_740_ = v___x_747_;
v_a_741_ = v_a_749_;
goto v___jp_739_;
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_745_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_745_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
lean_inc(v_a_750_);
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v___y_740_ = v___x_755_;
v_a_741_ = v_a_750_;
goto v___jp_739_;
}
}
}
v___jp_715_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_inc_ref(v___y_718_);
v___x_719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_719_, 0, v___y_718_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_717_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___y_716_);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_706_, v_toElabInfo_707_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
v___jp_729_:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Meta_ppExpr(v_expr_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_a_732_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
if (v_isBinder_709_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_716_ = v_a_730_;
v___y_717_ = v___x_736_;
v___y_718_ = v___x_737_;
goto v___jp_715_;
}
else
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_716_ = v_a_730_;
v___y_717_ = v___x_736_;
v___y_718_ = v___x_738_;
goto v___jp_715_;
}
}
else
{
lean_dec(v_a_730_);
lean_dec_ref(v_toElabInfo_707_);
lean_dec_ref(v_ctx_706_);
return v___x_731_;
}
}
v___jp_739_:
{
uint8_t v___x_742_; 
v___x_742_ = l_Lean_Exception_isInterrupt(v_a_741_);
if (v___x_742_ == 0)
{
uint8_t v___x_743_; 
v___x_743_ = l_Lean_Exception_isRuntime(v_a_741_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec_ref(v___y_740_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_730_ = v___x_744_;
goto v___jp_729_;
}
else
{
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_expr_708_);
lean_dec_ref(v_toElabInfo_707_);
lean_dec_ref(v_ctx_706_);
return v___y_740_;
}
}
else
{
lean_dec_ref(v_a_741_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_expr_708_);
lean_dec_ref(v_toElabInfo_707_);
lean_dec_ref(v_ctx_706_);
return v___y_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_758_, lean_object* v_toElabInfo_759_, lean_object* v_expr_760_, lean_object* v_isBinder_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v_isBinder_boxed_767_; lean_object* v_res_768_; 
v_isBinder_boxed_767_ = lean_unbox(v_isBinder_761_);
v_res_768_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_758_, v_toElabInfo_759_, v_expr_760_, v_isBinder_boxed_767_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_769_, lean_object* v_info_770_){
_start:
{
lean_object* v_toElabInfo_772_; lean_object* v_expr_773_; uint8_t v_isBinder_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_toElabInfo_772_ = lean_ctor_get(v_info_770_, 0);
v_expr_773_ = lean_ctor_get(v_info_770_, 3);
v_isBinder_774_ = lean_ctor_get_uint8(v_info_770_, sizeof(void*)*4);
v___x_775_ = lean_box(v_isBinder_774_);
lean_inc_ref(v_expr_773_);
lean_inc_ref(v_toElabInfo_772_);
lean_inc_ref(v_ctx_769_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_776_, 0, v_ctx_769_);
lean_closure_set(v___f_776_, 1, v_toElabInfo_772_);
lean_closure_set(v___f_776_, 2, v_expr_773_);
lean_closure_set(v___f_776_, 3, v___x_775_);
v___x_777_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_770_, v_ctx_769_, v___f_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_778_, lean_object* v_info_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Elab_TermInfo_format(v_ctx_778_, v_info_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_785_, lean_object* v_info_786_){
_start:
{
lean_object* v_toElabInfo_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_toElabInfo_787_ = lean_ctor_get(v_info_786_, 0);
lean_inc_ref(v_toElabInfo_787_);
lean_dec_ref(v_info_786_);
v___x_788_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_789_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_785_, v_toElabInfo_787_);
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v___x_798_; 
v___x_798_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_798_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_809_; 
v_val_799_ = lean_ctor_get(v_x_797_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_809_ == 0)
{
v___x_801_ = v_x_797_;
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_val_799_);
lean_dec(v_x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_803_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_804_ = lean_expr_dbg_to_string(v_val_799_);
lean_dec(v_val_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 3);
lean_ctor_set(v___x_801_, 0, v___x_804_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_803_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_816_, lean_object* v_lctx_817_, lean_object* v_stx_818_, lean_object* v_expectedType_x3f_819_, lean_object* v_info_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_845_; 
v___x_826_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_816_, v_lctx_817_, v_stx_818_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_845_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_831_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_a_827_);
v___x_833_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_819_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_Elab_CompletionInfo_stx(v_info_820_);
v___x_840_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_816_, v___x_839_);
lean_dec(v___x_839_);
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_838_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_841_);
v___x_843_ = v___x_829_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_846_, lean_object* v_lctx_847_, lean_object* v_stx_848_, lean_object* v_expectedType_x3f_849_, lean_object* v_info_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_846_, v_lctx_847_, v_stx_848_, v_expectedType_x3f_849_, v_info_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_info_850_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_863_, lean_object* v_info_864_){
_start:
{
switch(lean_obj_tag(v_info_864_))
{
case 0:
{
lean_object* v_termInfo_866_; lean_object* v_expectedType_x3f_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_888_; 
v_termInfo_866_ = lean_ctor_get(v_info_864_, 0);
v_expectedType_x3f_867_ = lean_ctor_get(v_info_864_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_info_864_);
if (v_isSharedCheck_888_ == 0)
{
v___x_869_ = v_info_864_;
v_isShared_870_ = v_isSharedCheck_888_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_expectedType_x3f_867_);
lean_inc(v_termInfo_866_);
lean_dec(v_info_864_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_888_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Elab_TermInfo_format(v_ctx_863_, v_termInfo_866_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_887_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 5);
lean_ctor_set(v___x_869_, 1, v_a_872_);
lean_ctor_set(v___x_869_, 0, v___x_876_);
v___x_878_ = v___x_869_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_872_);
v___x_878_ = v_reuseFailAlloc_886_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_879_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_867_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_del_object(v___x_869_);
lean_dec(v_expectedType_x3f_867_);
return v___x_871_;
}
}
}
case 1:
{
lean_object* v_stx_889_; lean_object* v_lctx_890_; lean_object* v_expectedType_x3f_891_; lean_object* v___f_892_; lean_object* v___x_893_; 
v_stx_889_ = lean_ctor_get(v_info_864_, 0);
lean_inc(v_stx_889_);
v_lctx_890_ = lean_ctor_get(v_info_864_, 2);
lean_inc_ref_n(v_lctx_890_, 2);
v_expectedType_x3f_891_ = lean_ctor_get(v_info_864_, 3);
lean_inc(v_expectedType_x3f_891_);
lean_inc_ref(v_ctx_863_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_892_, 0, v_ctx_863_);
lean_closure_set(v___f_892_, 1, v_lctx_890_);
lean_closure_set(v___f_892_, 2, v_stx_889_);
lean_closure_set(v___f_892_, 3, v_expectedType_x3f_891_);
lean_closure_set(v___f_892_, 4, v_info_864_);
v___x_893_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_863_, v_lctx_890_, v___f_892_);
return v___x_893_;
}
default: 
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_895_ = l_Lean_Elab_CompletionInfo_stx(v_info_864_);
lean_dec_ref(v_info_864_);
v___x_896_ = lean_box(0);
v___x_897_ = 0;
lean_inc(v___x_895_);
v___x_898_ = l_Lean_Syntax_formatStx(v___x_895_, v___x_896_, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_894_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_863_, v___x_895_);
lean_dec(v___x_895_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_905_, lean_object* v_info_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Elab_CompletionInfo_format(v_ctx_905_, v_info_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_912_, lean_object* v_info_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_916_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_912_, v_info_913_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_919_, lean_object* v_info_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_CommandInfo_format(v_ctx_919_, v_info_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_926_, lean_object* v_info_927_){
_start:
{
lean_object* v_stx_929_; lean_object* v_optionName_930_; lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_stx_929_ = lean_ctor_get(v_info_927_, 0);
lean_inc(v_stx_929_);
v_optionName_930_ = lean_ctor_get(v_info_927_, 1);
lean_inc(v_optionName_930_);
lean_dec_ref(v_info_927_);
v___x_931_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_932_ = 1;
v___x_933_ = l_Lean_Name_toString(v_optionName_930_, v___x_932_);
v___x_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_931_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_926_, v_stx_929_);
lean_dec(v_stx_929_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_941_, lean_object* v_info_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Elab_OptionInfo_format(v_ctx_941_, v_info_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_948_, lean_object* v_info_949_){
_start:
{
lean_object* v_stx_951_; lean_object* v_errorName_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_968_; 
v_stx_951_ = lean_ctor_get(v_info_949_, 0);
v_errorName_952_ = lean_ctor_get(v_info_949_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_info_949_);
if (v_isSharedCheck_968_ == 0)
{
v___x_954_ = v_info_949_;
v_isShared_955_ = v_isSharedCheck_968_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_errorName_952_);
lean_inc(v_stx_951_);
lean_dec(v_info_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_968_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_956_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_957_ = 1;
v___x_958_ = l_Lean_Name_toString(v_errorName_952_, v___x_957_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 5);
lean_ctor_set(v___x_954_, 1, v___x_959_);
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_961_ = v___x_954_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_967_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_948_, v_stx_951_);
lean_dec(v_stx_951_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_969_, lean_object* v_info_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_969_, v_info_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_979_, lean_object* v_fieldName_980_, lean_object* v_ctx_981_, lean_object* v_stx_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc_ref(v_val_979_);
v___x_988_ = lean_infer_type(v_val_979_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_Lean_Meta_ppExpr(v_a_989_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1021_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1021_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1021_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_ppExpr(v_val_979_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1020_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1000_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1001_ = 1;
v___x_1002_ = l_Lean_Name_toString(v_fieldName_980_, v___x_1001_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 3);
lean_ctor_set(v___x_993_, 0, v___x_1002_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_991_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_a_996_);
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_981_, v_stx_982_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1015_);
v___x_1017_ = v___x_998_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_del_object(v___x_993_);
lean_dec(v_a_991_);
lean_dec_ref(v_ctx_981_);
lean_dec(v_fieldName_980_);
return v___x_995_;
}
}
}
else
{
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v_ctx_981_);
lean_dec(v_fieldName_980_);
lean_dec_ref(v_val_979_);
return v___x_990_;
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v_ctx_981_);
lean_dec(v_fieldName_980_);
lean_dec_ref(v_val_979_);
v_a_1022_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_988_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_988_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1030_, lean_object* v_fieldName_1031_, lean_object* v_ctx_1032_, lean_object* v_stx_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1030_, v_fieldName_1031_, v_ctx_1032_, v_stx_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v_stx_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1040_, lean_object* v_info_1041_){
_start:
{
lean_object* v_fieldName_1043_; lean_object* v_lctx_1044_; lean_object* v_val_1045_; lean_object* v_stx_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
v_fieldName_1043_ = lean_ctor_get(v_info_1041_, 1);
lean_inc(v_fieldName_1043_);
v_lctx_1044_ = lean_ctor_get(v_info_1041_, 2);
lean_inc_ref(v_lctx_1044_);
v_val_1045_ = lean_ctor_get(v_info_1041_, 3);
lean_inc_ref(v_val_1045_);
v_stx_1046_ = lean_ctor_get(v_info_1041_, 4);
lean_inc(v_stx_1046_);
lean_dec_ref(v_info_1041_);
lean_inc_ref(v_ctx_1040_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1047_, 0, v_val_1045_);
lean_closure_set(v___f_1047_, 1, v_fieldName_1043_);
lean_closure_set(v___f_1047_, 2, v_ctx_1040_);
lean_closure_set(v___f_1047_, 3, v_stx_1046_);
v___x_1048_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1040_, v_lctx_1044_, v___f_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1049_, lean_object* v_info_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_FieldInfo_format(v_ctx_1049_, v_info_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_dec(v_pre_1053_);
return v_x_1054_;
}
else
{
lean_object* v_head_1056_; lean_object* v_tail_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1066_; 
v_head_1056_ = lean_ctor_get(v_x_1055_, 0);
v_tail_1057_ = lean_ctor_get(v_x_1055_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1059_ = v_x_1055_;
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_tail_1057_);
lean_inc(v_head_1056_);
lean_dec(v_x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
lean_inc(v_pre_1053_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 5);
lean_ctor_set(v___x_1059_, 1, v_pre_1053_);
lean_ctor_set(v___x_1059_, 0, v_x_1054_);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_x_1054_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_pre_1053_);
v___x_1062_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_head_1056_);
v_x_1054_ = v___x_1063_;
v_x_1055_ = v_tail_1057_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
lean_object* v___x_1069_; 
lean_dec(v_pre_1067_);
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
else
{
lean_object* v_head_1070_; lean_object* v_tail_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v_head_1070_ = lean_ctor_get(v_x_1068_, 0);
v_tail_1071_ = lean_ctor_get(v_x_1068_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1073_ = v_x_1068_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_tail_1071_);
lean_inc(v_head_1070_);
lean_dec(v_x_1068_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
lean_inc(v_pre_1067_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 5);
lean_ctor_set(v___x_1073_, 1, v_head_1070_);
lean_ctor_set(v___x_1073_, 0, v_pre_1067_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_pre_1067_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_head_1070_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1067_, v___x_1076_, v_tail_1071_);
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = l_List_reverse___redArg(v_x_1081_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v_head_1089_; lean_object* v_tail_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1108_; 
v_head_1089_ = lean_ctor_get(v_x_1080_, 0);
v_tail_1090_ = lean_ctor_get(v_x_1080_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1092_ = v_x_1080_;
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_tail_1090_);
lean_inc(v_head_1089_);
lean_dec(v_x_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Meta_ppGoal(v_head_1089_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v_head_1089_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v_x_1081_);
lean_ctor_set(v___x_1092_, 0, v_a_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1095_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_x_1081_);
v___x_1097_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v_x_1080_ = v_tail_1090_;
v_x_1081_ = v___x_1097_;
goto _start;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_del_object(v___x_1092_);
lean_dec(v_tail_1090_);
lean_dec(v_x_1081_);
v_a_1100_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1094_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1094_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1109_, v_x_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1120_, lean_object* v___x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1120_, v___x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1133_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1132_, v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1127_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1127_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1146_, lean_object* v___x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1146_, v___x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(32u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1159_ = ((size_t)5ULL);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_unsigned_to_nat(32u);
v___x_1162_ = lean_mk_empty_array_with_capacity(v___x_1161_);
v___x_1163_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1164_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
lean_ctor_set(v___x_1164_, 2, v___x_1160_);
lean_ctor_set(v___x_1164_, 3, v___x_1160_);
lean_ctor_set_usize(v___x_1164_, 4, v___x_1159_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = lean_box(1);
v___x_1166_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1167_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1166_);
lean_ctor_set(v___x_1168_, 2, v___x_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1172_, lean_object* v_goals_1173_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_List_isEmpty___redArg(v_goals_1173_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1177_ = lean_box(0);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1178_, 0, v_goals_1173_);
lean_closure_set(v___f_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1172_, v___x_1176_, v___f_1178_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_goals_1173_);
lean_dec_ref(v_ctx_1172_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1182_, lean_object* v_goals_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1182_, v_goals_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1195_, lean_object* v_info_1196_){
_start:
{
lean_object* v_toCommandContextInfo_1198_; lean_object* v_parentDecl_x3f_1199_; lean_object* v_autoImplicits_1200_; lean_object* v_env_1201_; lean_object* v_cmdEnv_x3f_1202_; lean_object* v_fileMap_1203_; lean_object* v_options_1204_; lean_object* v_currNamespace_1205_; lean_object* v_openDecls_1206_; lean_object* v_ngen_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1249_; 
v_toCommandContextInfo_1198_ = lean_ctor_get(v_ctx_1195_, 0);
lean_inc_ref(v_toCommandContextInfo_1198_);
v_parentDecl_x3f_1199_ = lean_ctor_get(v_ctx_1195_, 1);
v_autoImplicits_1200_ = lean_ctor_get(v_ctx_1195_, 2);
v_env_1201_ = lean_ctor_get(v_toCommandContextInfo_1198_, 0);
v_cmdEnv_x3f_1202_ = lean_ctor_get(v_toCommandContextInfo_1198_, 1);
v_fileMap_1203_ = lean_ctor_get(v_toCommandContextInfo_1198_, 2);
v_options_1204_ = lean_ctor_get(v_toCommandContextInfo_1198_, 4);
v_currNamespace_1205_ = lean_ctor_get(v_toCommandContextInfo_1198_, 5);
v_openDecls_1206_ = lean_ctor_get(v_toCommandContextInfo_1198_, 6);
v_ngen_1207_ = lean_ctor_get(v_toCommandContextInfo_1198_, 7);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_toCommandContextInfo_1198_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_toCommandContextInfo_1198_, 3);
lean_dec(v_unused_1250_);
v___x_1209_ = v_toCommandContextInfo_1198_;
v_isShared_1210_ = v_isSharedCheck_1249_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_ngen_1207_);
lean_inc(v_openDecls_1206_);
lean_inc(v_currNamespace_1205_);
lean_inc(v_options_1204_);
lean_inc(v_fileMap_1203_);
lean_inc(v_cmdEnv_x3f_1202_);
lean_inc(v_env_1201_);
lean_dec(v_toCommandContextInfo_1198_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1249_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_toElabInfo_1211_; lean_object* v_mctxBefore_1212_; lean_object* v_goalsBefore_1213_; lean_object* v_mctxAfter_1214_; lean_object* v_goalsAfter_1215_; lean_object* v___x_1217_; 
v_toElabInfo_1211_ = lean_ctor_get(v_info_1196_, 0);
lean_inc_ref(v_toElabInfo_1211_);
v_mctxBefore_1212_ = lean_ctor_get(v_info_1196_, 1);
lean_inc_ref(v_mctxBefore_1212_);
v_goalsBefore_1213_ = lean_ctor_get(v_info_1196_, 2);
lean_inc(v_goalsBefore_1213_);
v_mctxAfter_1214_ = lean_ctor_get(v_info_1196_, 3);
lean_inc_ref(v_mctxAfter_1214_);
v_goalsAfter_1215_ = lean_ctor_get(v_info_1196_, 4);
lean_inc(v_goalsAfter_1215_);
lean_dec_ref(v_info_1196_);
lean_inc_ref(v_ngen_1207_);
lean_inc(v_openDecls_1206_);
lean_inc(v_currNamespace_1205_);
lean_inc_ref(v_options_1204_);
lean_inc_ref(v_fileMap_1203_);
lean_inc(v_cmdEnv_x3f_1202_);
lean_inc_ref(v_env_1201_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 3, v_mctxBefore_1212_);
v___x_1217_ = v___x_1209_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_env_1201_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_cmdEnv_x3f_1202_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_fileMap_1203_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_mctxBefore_1212_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_options_1204_);
lean_ctor_set(v_reuseFailAlloc_1248_, 5, v_currNamespace_1205_);
lean_ctor_set(v_reuseFailAlloc_1248_, 6, v_openDecls_1206_);
lean_ctor_set(v_reuseFailAlloc_1248_, 7, v_ngen_1207_);
v___x_1217_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v_ctxB_1218_; lean_object* v___x_1219_; lean_object* v_ctxA_1220_; lean_object* v___x_1221_; 
lean_inc_ref_n(v_autoImplicits_1200_, 2);
lean_inc_n(v_parentDecl_x3f_1199_, 2);
v_ctxB_1218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1218_, 0, v___x_1217_);
lean_ctor_set(v_ctxB_1218_, 1, v_parentDecl_x3f_1199_);
lean_ctor_set(v_ctxB_1218_, 2, v_autoImplicits_1200_);
v___x_1219_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1219_, 0, v_env_1201_);
lean_ctor_set(v___x_1219_, 1, v_cmdEnv_x3f_1202_);
lean_ctor_set(v___x_1219_, 2, v_fileMap_1203_);
lean_ctor_set(v___x_1219_, 3, v_mctxAfter_1214_);
lean_ctor_set(v___x_1219_, 4, v_options_1204_);
lean_ctor_set(v___x_1219_, 5, v_currNamespace_1205_);
lean_ctor_set(v___x_1219_, 6, v_openDecls_1206_);
lean_ctor_set(v___x_1219_, 7, v_ngen_1207_);
v_ctxA_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1220_, 0, v___x_1219_);
lean_ctor_set(v_ctxA_1220_, 1, v_parentDecl_x3f_1199_);
lean_ctor_set(v_ctxA_1220_, 2, v_autoImplicits_1200_);
v___x_1221_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1218_, v_goalsBefore_1213_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1220_, v_goalsAfter_1215_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1247_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1247_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1247_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_stx_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v_stx_1228_ = lean_ctor_get(v_toElabInfo_1211_, 1);
lean_inc(v_stx_1228_);
v___x_1229_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1230_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1195_, v_toElabInfo_1211_);
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_box(0);
v___x_1235_ = 0;
v___x_1236_ = l_Lean_Syntax_formatStx(v_stx_1228_, v___x_1234_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1233_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_a_1222_);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1243_);
v___x_1245_ = v___x_1226_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_dec(v_a_1222_);
lean_dec_ref(v_toElabInfo_1211_);
lean_dec_ref(v_ctx_1195_);
return v___x_1223_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1220_, 3);
lean_dec(v_goalsAfter_1215_);
lean_dec_ref(v_toElabInfo_1211_);
lean_dec_ref(v_ctx_1195_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1251_, lean_object* v_info_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Elab_TacticInfo_format(v_ctx_1251_, v_info_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1261_, lean_object* v_info_1262_){
_start:
{
lean_object* v_lctx_1264_; lean_object* v_stx_1265_; lean_object* v_output_1266_; lean_object* v___x_1267_; lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1282_; 
v_lctx_1264_ = lean_ctor_get(v_info_1262_, 0);
lean_inc_ref_n(v_lctx_1264_, 2);
v_stx_1265_ = lean_ctor_get(v_info_1262_, 1);
lean_inc(v_stx_1265_);
v_output_1266_ = lean_ctor_get(v_info_1262_, 2);
lean_inc(v_output_1266_);
lean_dec_ref(v_info_1262_);
v___x_1267_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1261_, v_lctx_1264_, v_stx_1265_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1261_, v_lctx_1264_, v_output_1266_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1274_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v_a_1268_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1278_);
v___x_1280_ = v___x_1272_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1283_, lean_object* v_info_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1283_, v_info_1284_);
lean_dec_ref(v_ctx_1283_);
return v_res_1286_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = 1;
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1292_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set_usize(v___x_1292_, 2, v___x_1290_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3, v___x_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1296_){
_start:
{
lean_object* v_toWidgetInstance_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1326_; 
v_toWidgetInstance_1297_ = lean_ctor_get(v_info_1296_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_info_1296_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_info_1296_, 1);
lean_dec(v_unused_1327_);
v___x_1299_ = v_info_1296_;
v_isShared_1300_ = v_isSharedCheck_1326_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_toWidgetInstance_1297_);
lean_dec(v_info_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1326_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_id_1301_; lean_object* v_props_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_fst_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1324_; 
v_id_1301_ = lean_ctor_get(v_toWidgetInstance_1297_, 0);
lean_inc(v_id_1301_);
v_props_1302_ = lean_ctor_get(v_toWidgetInstance_1297_, 1);
lean_inc_ref(v_props_1302_);
lean_dec_ref(v_toWidgetInstance_1297_);
v___x_1303_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1304_ = lean_apply_1(v_props_1302_, v___x_1303_);
v_fst_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1304_, 1);
lean_dec(v_unused_1325_);
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1324_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_fst_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1324_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1309_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1310_ = 1;
v___x_1311_ = l_Lean_Name_toString(v_id_1301_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 5);
lean_ctor_set(v___x_1307_, 1, v___x_1312_);
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1314_ = v___x_1307_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 5);
lean_ctor_set(v___x_1299_, 1, v___x_1315_);
lean_ctor_set(v___x_1299_, 0, v___x_1314_);
v___x_1317_ = v___x_1299_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_unsigned_to_nat(80u);
v___x_1319_ = l_Lean_Json_pretty(v_fst_1305_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1317_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1334_){
_start:
{
lean_object* v_userName_1335_; lean_object* v_id_1336_; lean_object* v_baseId_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_userName_1335_ = lean_ctor_get(v_info_1334_, 0);
lean_inc(v_userName_1335_);
v_id_1336_ = lean_ctor_get(v_info_1334_, 1);
lean_inc(v_id_1336_);
v_baseId_1337_ = lean_ctor_get(v_info_1334_, 2);
lean_inc(v_baseId_1337_);
lean_dec_ref(v_info_1334_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1339_ = l_Lean_Name_eraseMacroScopes(v_userName_1335_);
lean_dec(v_userName_1335_);
v___x_1340_ = 1;
v___x_1341_ = l_Lean_Name_toString(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1338_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_Name_toString(v_id_1336_, v___x_1340_);
v___x_1347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1345_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = l_Lean_Name_toString(v_baseId_1337_, v___x_1340_);
v___x_1352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1350_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1357_, lean_object* v_info_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1360_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1357_, v_info_1358_);
v___x_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1362_, lean_object* v_info_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1362_, v_info_1363_);
lean_dec(v_info_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1367_, lean_object* v_info_1368_){
_start:
{
lean_object* v_mkDocString_x3f_1370_; 
v_mkDocString_x3f_1370_ = lean_ctor_get(v_info_1368_, 2);
lean_inc(v_mkDocString_x3f_1370_);
lean_dec_ref(v_info_1368_);
if (lean_obj_tag(v_mkDocString_x3f_1370_) == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_ppCtx_1367_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
else
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1405_; 
v_val_1373_ = lean_ctor_get(v_mkDocString_x3f_1370_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_mkDocString_x3f_1370_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1375_ = v_mkDocString_x3f_1370_;
v_isShared_1376_ = v_isSharedCheck_1405_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v_mkDocString_x3f_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1405_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_apply_2(v_val_1373_, v_ppCtx_1367_, lean_box(0));
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1388_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_a_1378_);
v___x_1383_ = v___x_1375_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
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
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1404_; 
v_a_1389_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1391_ = v___x_1377_;
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1377_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1393_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1394_ = lean_io_error_to_string(v_a_1389_);
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1397_);
v___x_1399_ = v___x_1375_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1399_);
v___x_1401_ = v___x_1391_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1406_, lean_object* v_info_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1406_, v_info_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1412_;
}
else
{
lean_object* v_val_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1424_; 
v_val_1413_ = lean_ctor_get(v_x_1410_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1415_ = v_x_1410_;
v_isShared_1416_ = v_isSharedCheck_1424_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_val_1413_);
lean_dec(v_x_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1424_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1418_ = l_String_quote(v_val_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 3);
lean_ctor_set(v___x_1415_, 0, v___x_1418_);
v___x_1420_ = v___x_1415_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1417_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Repr_addAppParen(v___x_1421_, v_x_1411_);
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1425_, v_x_1426_);
lean_dec(v_x_1426_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1442_, lean_object* v_info_1443_){
_start:
{
lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v_toTermInfo_1451_; lean_object* v_location_x3f_1452_; uint8_t v_explicit_1453_; lean_object* v___y_1455_; 
v_toTermInfo_1451_ = lean_ctor_get(v_info_1443_, 0);
lean_inc_ref(v_toTermInfo_1451_);
v_location_x3f_1452_ = lean_ctor_get(v_info_1443_, 1);
lean_inc(v_location_x3f_1452_);
v_explicit_1453_ = lean_ctor_get_uint8(v_info_1443_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1452_) == 1)
{
lean_object* v_val_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1537_; 
v_val_1476_ = lean_ctor_get(v_location_x3f_1452_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_location_x3f_1452_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1478_ = v_location_x3f_1452_;
v_isShared_1479_ = v_isSharedCheck_1537_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_val_1476_);
lean_dec(v_location_x3f_1452_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1537_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_range_1480_; lean_object* v_pos_1481_; lean_object* v_endPos_1482_; lean_object* v_module_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1535_; 
v_range_1480_ = lean_ctor_get(v_val_1476_, 1);
v_pos_1481_ = lean_ctor_get(v_range_1480_, 0);
lean_inc_ref(v_pos_1481_);
v_endPos_1482_ = lean_ctor_get(v_range_1480_, 2);
lean_inc_ref(v_endPos_1482_);
v_module_1483_ = lean_ctor_get(v_val_1476_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_val_1476_, 1);
lean_dec(v_unused_1536_);
v___x_1485_ = v_val_1476_;
v_isShared_1486_ = v_isSharedCheck_1535_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_module_1483_);
lean_dec(v_val_1476_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1535_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_line_1487_; lean_object* v_column_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1534_; 
v_line_1487_ = lean_ctor_get(v_pos_1481_, 0);
v_column_1488_ = lean_ctor_get(v_pos_1481_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_pos_1481_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1490_ = v_pos_1481_;
v_isShared_1491_ = v_isSharedCheck_1534_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_column_1488_);
lean_inc(v_line_1487_);
lean_dec(v_pos_1481_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1534_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_line_1492_; lean_object* v_column_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1533_; 
v_line_1492_ = lean_ctor_get(v_endPos_1482_, 0);
v_column_1493_ = lean_ctor_get(v_endPos_1482_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_endPos_1482_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1495_ = v_endPos_1482_;
v_isShared_1496_ = v_isSharedCheck_1533_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_column_1493_);
lean_inc(v_line_1492_);
lean_dec(v_endPos_1482_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1533_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = 1;
v___x_1498_ = l_Lean_Name_toString(v_module_1483_, v___x_1497_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 3);
lean_ctor_set(v___x_1478_, 0, v___x_1498_);
v___x_1500_ = v___x_1478_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 5);
lean_ctor_set(v___x_1495_, 1, v___x_1501_);
lean_ctor_set(v___x_1495_, 0, v___x_1500_);
v___x_1503_ = v___x_1495_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1505_ = l_Nat_reprFast(v_line_1487_);
v___x_1506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 5);
lean_ctor_set(v___x_1490_, 1, v___x_1506_);
lean_ctor_set(v___x_1490_, 0, v___x_1504_);
v___x_1508_ = v___x_1490_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 5);
lean_ctor_set(v___x_1485_, 1, v___x_1509_);
lean_ctor_set(v___x_1485_, 0, v___x_1508_);
v___x_1511_ = v___x_1485_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1512_ = l_Nat_reprFast(v_column_1488_);
v___x_1513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1511_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1503_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Nat_reprFast(v_line_1492_);
v___x_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1504_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1509_);
v___x_1524_ = l_Nat_reprFast(v_column_1493_);
v___x_1525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1523_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1515_);
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1519_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___y_1455_ = v___x_1528_;
goto v___jp_1454_;
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
lean_object* v___x_1538_; 
lean_dec(v_location_x3f_1452_);
v___x_1538_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1455_ = v___x_1538_;
goto v___jp_1454_;
}
v___jp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_inc_ref(v___y_1447_);
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1447_);
v___x_1449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1446_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
v___jp_1454_:
{
lean_object* v_lctx_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_lctx_1456_ = lean_ctor_get(v_toTermInfo_1451_, 1);
lean_inc_ref(v_lctx_1456_);
v___x_1457_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1442_, v_lctx_1456_);
v___x_1458_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1457_, v_info_1443_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = l_Lean_Elab_TermInfo_format(v_ctx_1442_, v_toTermInfo_1451_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v_a_1461_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___y_1455_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1459_, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1468_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
if (v_explicit_1453_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1446_ = v___x_1473_;
v___y_1447_ = v___x_1474_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1446_ = v___x_1473_;
v___y_1447_ = v___x_1475_;
goto v___jp_1445_;
}
}
else
{
lean_dec(v_a_1459_);
lean_dec(v___y_1455_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1539_, lean_object* v_info_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1539_, v_info_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1546_, lean_object* v_info_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1549_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1546_, v_info_1547_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1563_, lean_object* v_info_1564_){
_start:
{
lean_object* v_stx_1565_; lean_object* v_chosenAltIdx_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1594_; 
v_stx_1565_ = lean_ctor_get(v_info_1564_, 0);
v_chosenAltIdx_1566_ = lean_ctor_get(v_info_1564_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_info_1564_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1568_ = v_info_1564_;
v_isShared_1569_ = v_isSharedCheck_1594_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_chosenAltIdx_1566_);
lean_inc(v_stx_1565_);
lean_dec(v_info_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1594_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1570_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1566_);
v___x_1571_ = l_Nat_reprFast(v_chosenAltIdx_1566_);
v___x_1572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 5);
lean_ctor_set(v___x_1568_, 1, v___x_1572_);
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1575_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_Syntax_getNumArgs(v_stx_1565_);
v___x_1578_ = l_Nat_reprFast(v___x_1577_);
v___x_1579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1576_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_Syntax_getArg(v_stx_1565_, v_chosenAltIdx_1566_);
lean_dec(v_chosenAltIdx_1566_);
v___x_1584_ = l_Lean_Syntax_getKind(v___x_1583_);
v___x_1585_ = 1;
v___x_1586_ = l_Lean_Name_toString(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1582_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1563_, v_stx_1565_);
lean_dec(v_stx_1565_);
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1598_, lean_object* v_info_1599_){
_start:
{
lean_object* v_stx_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_stx_1600_ = lean_ctor_get(v_info_1599_, 1);
v___x_1601_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1600_);
v___x_1602_ = l_Lean_Syntax_getKind(v_stx_1600_);
v___x_1603_ = 1;
v___x_1604_ = l_Lean_Name_toString(v___x_1602_, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1598_, v_info_1599_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1614_, lean_object* v_info_1615_){
_start:
{
lean_object* v_toElabInfo_1616_; lean_object* v_name_1617_; uint8_t v_kind_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_toElabInfo_1616_ = lean_ctor_get(v_info_1615_, 0);
lean_inc_ref(v_toElabInfo_1616_);
v_name_1617_ = lean_ctor_get(v_info_1615_, 1);
lean_inc(v_name_1617_);
v_kind_1618_ = lean_ctor_get_uint8(v_info_1615_, sizeof(void*)*2);
lean_dec_ref(v_info_1615_);
v___x_1619_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1620_ = 1;
v___x_1621_ = l_Lean_Name_toString(v_name_1617_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1619_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1618_, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1614_, v_toElabInfo_1616_);
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1633_, lean_object* v_x_1634_){
_start:
{
switch(lean_obj_tag(v_x_1634_))
{
case 0:
{
lean_object* v_i_1636_; lean_object* v___x_1637_; 
v_i_1636_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1636_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1637_ = l_Lean_Elab_TacticInfo_format(v_ctx_1633_, v_i_1636_);
return v___x_1637_;
}
case 1:
{
lean_object* v_i_1638_; lean_object* v___x_1639_; 
v_i_1638_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1638_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1639_ = l_Lean_Elab_TermInfo_format(v_ctx_1633_, v_i_1638_);
return v___x_1639_;
}
case 2:
{
lean_object* v_i_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_i_1640_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v_x_1634_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_i_1640_);
lean_dec(v_x_1634_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1633_, v_i_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
case 3:
{
lean_object* v_i_1649_; lean_object* v___x_1650_; 
v_i_1649_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1649_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1650_ = l_Lean_Elab_CommandInfo_format(v_ctx_1633_, v_i_1649_);
return v___x_1650_;
}
case 4:
{
lean_object* v_i_1651_; lean_object* v___x_1652_; 
v_i_1651_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1651_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1652_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1633_, v_i_1651_);
lean_dec_ref(v_ctx_1633_);
return v___x_1652_;
}
case 5:
{
lean_object* v_i_1653_; lean_object* v___x_1654_; 
v_i_1653_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1653_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1654_ = l_Lean_Elab_OptionInfo_format(v_ctx_1633_, v_i_1653_);
return v___x_1654_;
}
case 6:
{
lean_object* v_i_1655_; lean_object* v___x_1656_; 
v_i_1655_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1655_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1656_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1633_, v_i_1655_);
return v___x_1656_;
}
case 7:
{
lean_object* v_i_1657_; lean_object* v___x_1658_; 
v_i_1657_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1657_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1658_ = l_Lean_Elab_FieldInfo_format(v_ctx_1633_, v_i_1657_);
return v___x_1658_;
}
case 8:
{
lean_object* v_i_1659_; lean_object* v___x_1660_; 
v_i_1659_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1659_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1660_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1633_, v_i_1659_);
return v___x_1660_;
}
case 9:
{
lean_object* v_i_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_ctx_1633_);
v_i_1661_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v_x_1634_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_i_1661_);
lean_dec(v_x_1634_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
case 10:
{
lean_object* v_i_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v_ctx_1633_);
v_i_1670_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1672_ = v_x_1634_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_i_1670_);
lean_dec(v_x_1634_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = l_Lean_Elab_CustomInfo_format(v_i_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
case 11:
{
lean_object* v_i_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_ctx_1633_);
v_i_1679_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v_x_1634_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_i_1679_);
lean_dec(v_x_1634_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
case 12:
{
lean_object* v_i_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
v_i_1688_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v_x_1634_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_i_1688_);
lean_dec(v_x_1634_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1633_, v_i_1688_);
lean_dec(v_i_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
case 13:
{
lean_object* v_i_1697_; lean_object* v___x_1698_; 
v_i_1697_ = lean_ctor_get(v_x_1634_, 0);
lean_inc_ref(v_i_1697_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1698_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1633_, v_i_1697_);
return v___x_1698_;
}
case 14:
{
lean_object* v_i_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_i_1699_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v_x_1634_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_i_1699_);
lean_dec(v_x_1634_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1633_, v_i_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
case 15:
{
lean_object* v_i_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_i_1708_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1710_ = v_x_1634_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_i_1708_);
lean_dec(v_x_1634_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1633_, v_i_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
case 16:
{
lean_object* v_i_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_i_1717_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v_x_1634_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_i_1717_);
lean_dec(v_x_1634_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = l_Lean_Elab_DocInfo_format(v_ctx_1633_, v_i_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
default: 
{
lean_object* v_i_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_i_1726_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v_x_1634_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_i_1726_);
lean_dec(v_x_1634_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1633_, v_i_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1735_, lean_object* v_x_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Elab_Info_format(v_ctx_1735_, v_x_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
return v_x_1739_;
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_head_1741_ = lean_ctor_get(v_x_1740_, 0);
v_tail_1742_ = lean_ctor_get(v_x_1740_, 1);
v___x_1743_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1744_ = lean_string_append(v_x_1739_, v___x_1743_);
v___x_1745_ = lean_expr_dbg_to_string(v_head_1741_);
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
lean_dec_ref(v___x_1745_);
v_x_1739_ = v___x_1746_;
v_x_1740_ = v_tail_1742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1748_, v_x_1749_);
lean_dec(v_x_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1754_;
}
else
{
lean_object* v_tail_1755_; 
v_tail_1755_ = lean_ctor_get(v_x_1753_, 1);
if (lean_obj_tag(v_tail_1755_) == 0)
{
lean_object* v_head_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_head_1756_ = lean_ctor_get(v_x_1753_, 0);
v___x_1757_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1758_ = lean_expr_dbg_to_string(v_head_1756_);
v___x_1759_ = lean_string_append(v___x_1757_, v___x_1758_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v_head_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint32_t v___x_1767_; lean_object* v___x_1768_; 
v_head_1762_ = lean_ctor_get(v_x_1753_, 0);
v___x_1763_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1764_ = lean_expr_dbg_to_string(v_head_1762_);
v___x_1765_ = lean_string_append(v___x_1763_, v___x_1764_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1765_, v_tail_1755_);
v___x_1767_ = 93;
v___x_1768_ = lean_string_push(v___x_1766_, v___x_1767_);
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1769_);
lean_dec(v_x_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1777_){
_start:
{
switch(lean_obj_tag(v_ctx_1777_))
{
case 0:
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v_ctx_1777_, 1);
v___x_1778_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1778_;
}
case 1:
{
lean_object* v_parentDecl_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_parentDecl_1779_ = lean_ctor_get(v_ctx_1777_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_ctx_1777_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1781_ = v_ctx_1777_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_parentDecl_1779_);
lean_dec(v_ctx_1777_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1783_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1784_ = 1;
v___x_1785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1779_, v___x_1784_);
v___x_1786_ = lean_string_append(v___x_1783_, v___x_1785_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 3);
lean_ctor_set(v___x_1781_, 0, v___x_1788_);
v___x_1790_ = v___x_1781_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1808_; 
v_autoImplicits_1793_ = lean_ctor_get(v_ctx_1777_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_ctx_1777_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1795_ = v_ctx_1777_;
v_isShared_1796_ = v_isSharedCheck_1808_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_autoImplicits_1793_);
lean_dec(v_ctx_1777_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1808_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1797_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1798_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1799_ = lean_array_to_list(v_autoImplicits_1793_);
v___x_1800_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1799_);
lean_dec(v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1798_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = lean_string_append(v___x_1797_, v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1804_ = lean_string_append(v___x_1802_, v___x_1803_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 3);
lean_ctor_set(v___x_1795_, 0, v___x_1804_);
v___x_1806_ = v___x_1795_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1818_, lean_object* v_ctx_x3f_1819_){
_start:
{
switch(lean_obj_tag(v_tree_1818_))
{
case 0:
{
lean_object* v_i_1821_; lean_object* v_t_1822_; lean_object* v___x_1823_; 
v_i_1821_ = lean_ctor_get(v_tree_1818_, 0);
lean_inc_ref(v_i_1821_);
v_t_1822_ = lean_ctor_get(v_tree_1818_, 1);
lean_inc_ref(v_t_1822_);
lean_dec_ref_known(v_tree_1818_, 2);
v___x_1823_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1821_, v_ctx_x3f_1819_);
v_tree_1818_ = v_t_1822_;
v_ctx_x3f_1819_ = v___x_1823_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1819_) == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec_ref_known(v_tree_1818_, 2);
v___x_1825_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
else
{
lean_object* v_i_1827_; lean_object* v_children_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1878_; 
v_i_1827_ = lean_ctor_get(v_tree_1818_, 0);
v_children_1828_ = lean_ctor_get(v_tree_1818_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_tree_1818_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1830_ = v_tree_1818_;
v_isShared_1831_ = v_isSharedCheck_1878_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_children_1828_);
lean_inc(v_i_1827_);
lean_dec(v_tree_1818_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1878_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_val_1832_; lean_object* v___x_1833_; 
v_val_1832_ = lean_ctor_get(v_ctx_x3f_1819_, 0);
lean_inc_ref(v_i_1827_);
lean_inc(v_val_1832_);
v___x_1833_ = l_Lean_Elab_Info_format(v_val_1832_, v_i_1827_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1877_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1877_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1877_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_size_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_size_1838_ = lean_ctor_get(v_children_1828_, 2);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_size_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_del_object(v___x_1836_);
v___x_1841_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1819_, v_i_1827_);
lean_dec_ref(v_i_1827_);
v___x_1842_ = l_Lean_PersistentArray_toList___redArg(v_children_1828_);
lean_dec_ref(v_children_1828_);
v___x_1843_ = lean_box(0);
v___x_1844_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1841_, v___x_1842_, v___x_1843_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1860_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1860_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1860_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 5);
lean_ctor_set(v___x_1830_, 1, v_a_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1849_);
v___x_1851_ = v___x_1830_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1834_);
v___x_1851_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1852_ = lean_box(1);
v___x_1853_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1852_, v_a_1845_);
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Std_Format_nestD(v___x_1854_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1855_);
v___x_1857_ = v___x_1847_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1834_);
lean_del_object(v___x_1830_);
v_a_1861_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1844_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1844_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v_children_1828_);
lean_dec_ref(v_i_1827_);
lean_dec_ref_known(v_ctx_x3f_1819_, 1);
v___x_1869_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 5);
lean_ctor_set(v___x_1830_, 1, v_a_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1869_);
v___x_1871_ = v___x_1830_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_a_1834_);
v___x_1871_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = l_Std_Format_nestD(v___x_1871_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1872_);
v___x_1874_ = v___x_1836_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
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
}
else
{
lean_del_object(v___x_1830_);
lean_dec_ref(v_children_1828_);
lean_dec_ref(v_i_1827_);
lean_dec_ref_known(v_ctx_x3f_1819_, 1);
return v___x_1833_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_ctx_x3f_1819_);
v_mvarId_1879_ = lean_ctor_get(v_tree_1818_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_tree_1818_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1881_ = v_tree_1818_;
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_mvarId_1879_);
lean_dec(v_tree_1818_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1883_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1884_ = 1;
v___x_1885_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1879_, v___x_1884_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 3);
lean_ctor_set(v___x_1881_, 0, v___x_1885_);
v___x_1887_ = v___x_1881_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1883_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Std_Format_nestD(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v___x_1893_);
v___x_1897_ = l_List_reverse___redArg(v_x_1895_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v_head_1899_; lean_object* v_tail_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1918_; 
v_head_1899_ = lean_ctor_get(v_x_1894_, 0);
v_tail_1900_ = lean_ctor_get(v_x_1894_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_x_1894_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1902_ = v_x_1894_;
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_tail_1900_);
lean_inc(v_head_1899_);
lean_dec(v_x_1894_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; 
lean_inc(v___x_1893_);
v___x_1904_ = l_Lean_Elab_InfoTree_format(v_head_1899_, v___x_1893_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_x_1895_);
lean_ctor_set(v___x_1902_, 0, v_a_1905_);
v___x_1907_ = v___x_1902_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1905_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_x_1895_);
v___x_1907_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v_x_1894_ = v_tail_1900_;
v_x_1895_ = v___x_1907_;
goto _start;
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1902_);
lean_dec(v_tail_1900_);
lean_dec(v_x_1895_);
lean_dec(v___x_1893_);
v_a_1910_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1904_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1904_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1919_, v_x_1920_, v_x_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1924_, lean_object* v_ctx_x3f_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Elab_InfoTree_format(v_tree_1924_, v_ctx_x3f_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1928_, lean_object* v_s_1929_){
_start:
{
uint8_t v_enabled_1930_; lean_object* v_assignment_1931_; lean_object* v_lazyAssignment_1932_; lean_object* v_trees_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v_enabled_1930_ = lean_ctor_get_uint8(v_s_1929_, sizeof(void*)*3);
v_assignment_1931_ = lean_ctor_get(v_s_1929_, 0);
v_lazyAssignment_1932_ = lean_ctor_get(v_s_1929_, 1);
v_trees_1933_ = lean_ctor_get(v_s_1929_, 2);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_s_1929_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1935_ = v_s_1929_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_trees_1933_);
lean_inc(v_lazyAssignment_1932_);
lean_inc(v_assignment_1931_);
lean_dec(v_s_1929_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = lean_apply_1(v_f_1928_, v_trees_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 2, v___x_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_assignment_1931_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_lazyAssignment_1932_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v___x_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1940_, sizeof(void*)*3, v_enabled_1930_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1942_, lean_object* v_f_1943_){
_start:
{
lean_object* v_modifyInfoState_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; 
v_modifyInfoState_1944_ = lean_ctor_get(v_inst_1942_, 1);
lean_inc(v_modifyInfoState_1944_);
lean_dec_ref(v_inst_1942_);
v___f_1945_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1945_, 0, v_f_1943_);
v___x_1946_ = lean_apply_1(v_modifyInfoState_1944_, v___f_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1947_, lean_object* v_inst_1948_, lean_object* v_f_1949_){
_start:
{
lean_object* v_modifyInfoState_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; 
v_modifyInfoState_1950_ = lean_ctor_get(v_inst_1948_, 1);
lean_inc(v_modifyInfoState_1950_);
lean_dec_ref(v_inst_1948_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1951_, 0, v_f_1949_);
v___x_1952_ = lean_apply_1(v_modifyInfoState_1950_, v___f_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_unsigned_to_nat(32u);
v___x_1954_ = lean_mk_empty_array_with_capacity(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1956_ = ((size_t)5ULL);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_unsigned_to_nat(32u);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1958_);
v___x_1960_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1961_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set(v___x_1961_, 2, v___x_1957_);
lean_ctor_set(v___x_1961_, 3, v___x_1957_);
lean_ctor_set_usize(v___x_1961_, 4, v___x_1956_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1962_){
_start:
{
uint8_t v_enabled_1963_; lean_object* v_assignment_1964_; lean_object* v_lazyAssignment_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_enabled_1963_ = lean_ctor_get_uint8(v_s_1962_, sizeof(void*)*3);
v_assignment_1964_ = lean_ctor_get(v_s_1962_, 0);
v_lazyAssignment_1965_ = lean_ctor_get(v_s_1962_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_s_1962_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_s_1962_, 2);
lean_dec(v_unused_1974_);
v___x_1967_ = v_s_1962_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_lazyAssignment_1965_);
lean_inc(v_assignment_1964_);
lean_dec(v_s_1962_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 2, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_assignment_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_lazyAssignment_1965_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v___x_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*3, v_enabled_1963_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1975_, lean_object* v_trees_1976_, lean_object* v_____r_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_apply_2(v_toPure_1975_, lean_box(0), v_trees_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1979_, lean_object* v_modifyInfoState_1980_, lean_object* v___f_1981_, lean_object* v_toBind_1982_, lean_object* v_____do__lift_1983_){
_start:
{
lean_object* v_trees_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_trees_1984_ = lean_ctor_get(v_____do__lift_1983_, 2);
lean_inc_ref(v_trees_1984_);
lean_dec_ref(v_____do__lift_1983_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1985_, 0, v_toPure_1979_);
lean_closure_set(v___f_1985_, 1, v_trees_1984_);
v___x_1986_ = lean_apply_1(v_modifyInfoState_1980_, v___f_1981_);
v___x_1987_ = lean_apply_4(v_toBind_1982_, lean_box(0), lean_box(0), v___x_1986_, v___f_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1989_, lean_object* v_inst_1990_){
_start:
{
lean_object* v_toApplicative_1991_; lean_object* v_toBind_1992_; lean_object* v_getInfoState_1993_; lean_object* v_modifyInfoState_1994_; lean_object* v_toPure_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; 
v_toApplicative_1991_ = lean_ctor_get(v_inst_1989_, 0);
lean_inc_ref(v_toApplicative_1991_);
v_toBind_1992_ = lean_ctor_get(v_inst_1989_, 1);
lean_inc_n(v_toBind_1992_, 2);
lean_dec_ref(v_inst_1989_);
v_getInfoState_1993_ = lean_ctor_get(v_inst_1990_, 0);
lean_inc(v_getInfoState_1993_);
v_modifyInfoState_1994_ = lean_ctor_get(v_inst_1990_, 1);
lean_inc(v_modifyInfoState_1994_);
lean_dec_ref(v_inst_1990_);
v_toPure_1995_ = lean_ctor_get(v_toApplicative_1991_, 1);
lean_inc(v_toPure_1995_);
lean_dec_ref(v_toApplicative_1991_);
v___f_1996_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1997_, 0, v_toPure_1995_);
lean_closure_set(v___f_1997_, 1, v_modifyInfoState_1994_);
lean_closure_set(v___f_1997_, 2, v___f_1996_);
lean_closure_set(v___f_1997_, 3, v_toBind_1992_);
v___x_1998_ = lean_apply_4(v_toBind_1992_, lean_box(0), lean_box(0), v_getInfoState_1993_, v___f_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2000_, v_inst_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2003_, lean_object* v_s_2004_){
_start:
{
uint8_t v_enabled_2005_; lean_object* v_assignment_2006_; lean_object* v_lazyAssignment_2007_; lean_object* v_trees_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_enabled_2005_ = lean_ctor_get_uint8(v_s_2004_, sizeof(void*)*3);
v_assignment_2006_ = lean_ctor_get(v_s_2004_, 0);
v_lazyAssignment_2007_ = lean_ctor_get(v_s_2004_, 1);
v_trees_2008_ = lean_ctor_get(v_s_2004_, 2);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_s_2004_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v_s_2004_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_trees_2008_);
lean_inc(v_lazyAssignment_2007_);
lean_inc(v_assignment_2006_);
lean_dec(v_s_2004_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_PersistentArray_push___redArg(v_trees_2008_, v_t_2003_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 2, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_assignment_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_lazyAssignment_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v___x_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*3, v_enabled_2005_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2017_, lean_object* v_modifyInfoState_2018_, lean_object* v___f_2019_, lean_object* v_____do__lift_2020_){
_start:
{
uint8_t v_enabled_2021_; 
v_enabled_2021_ = lean_ctor_get_uint8(v_____do__lift_2020_, sizeof(void*)*3);
if (v_enabled_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v___f_2019_);
lean_dec(v_modifyInfoState_2018_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_apply_2(v_toPure_2017_, lean_box(0), v___x_2022_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; 
lean_dec(v_toPure_2017_);
v___x_2024_ = lean_apply_1(v_modifyInfoState_2018_, v___f_2019_);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2025_, lean_object* v_modifyInfoState_2026_, lean_object* v___f_2027_, lean_object* v_____do__lift_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2025_, v_modifyInfoState_2026_, v___f_2027_, v_____do__lift_2028_);
lean_dec_ref(v_____do__lift_2028_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_t_2032_){
_start:
{
lean_object* v_toApplicative_2033_; lean_object* v_toBind_2034_; lean_object* v_getInfoState_2035_; lean_object* v_modifyInfoState_2036_; lean_object* v_toPure_2037_; lean_object* v___f_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; 
v_toApplicative_2033_ = lean_ctor_get(v_inst_2030_, 0);
lean_inc_ref(v_toApplicative_2033_);
v_toBind_2034_ = lean_ctor_get(v_inst_2030_, 1);
lean_inc(v_toBind_2034_);
lean_dec_ref(v_inst_2030_);
v_getInfoState_2035_ = lean_ctor_get(v_inst_2031_, 0);
lean_inc(v_getInfoState_2035_);
v_modifyInfoState_2036_ = lean_ctor_get(v_inst_2031_, 1);
lean_inc(v_modifyInfoState_2036_);
lean_dec_ref(v_inst_2031_);
v_toPure_2037_ = lean_ctor_get(v_toApplicative_2033_, 1);
lean_inc(v_toPure_2037_);
lean_dec_ref(v_toApplicative_2033_);
v___f_2038_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2038_, 0, v_t_2032_);
v___f_2039_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2039_, 0, v_toPure_2037_);
lean_closure_set(v___f_2039_, 1, v_modifyInfoState_2036_);
lean_closure_set(v___f_2039_, 2, v___f_2038_);
v___x_2040_ = lean_apply_4(v_toBind_2034_, lean_box(0), lean_box(0), v_getInfoState_2035_, v___f_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_t_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2042_, v_inst_2043_, v_t_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2046_, lean_object* v_t_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_____do__lift_2050_){
_start:
{
uint8_t v_enabled_2051_; 
v_enabled_2051_ = lean_ctor_get_uint8(v_____do__lift_2050_, sizeof(void*)*3);
if (v_enabled_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v_inst_2049_);
lean_dec_ref(v_inst_2048_);
lean_dec_ref(v_t_2047_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_apply_2(v_toPure_2046_, lean_box(0), v___x_2052_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_toPure_2046_);
v___x_2054_ = lean_unsigned_to_nat(32u);
v___x_2055_ = lean_mk_empty_array_with_capacity(v___x_2054_);
lean_dec_ref(v___x_2055_);
v___x_2056_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_t_2047_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2048_, v_inst_2049_, v___x_2057_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2059_, lean_object* v_t_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_____do__lift_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2059_, v_t_2060_, v_inst_2061_, v_inst_2062_, v_____do__lift_2063_);
lean_dec_ref(v_____do__lift_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_t_2067_){
_start:
{
lean_object* v_toApplicative_2068_; lean_object* v_toBind_2069_; lean_object* v_getInfoState_2070_; lean_object* v_toPure_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; 
v_toApplicative_2068_ = lean_ctor_get(v_inst_2065_, 0);
v_toBind_2069_ = lean_ctor_get(v_inst_2065_, 1);
lean_inc(v_toBind_2069_);
v_getInfoState_2070_ = lean_ctor_get(v_inst_2066_, 0);
lean_inc(v_getInfoState_2070_);
v_toPure_2071_ = lean_ctor_get(v_toApplicative_2068_, 1);
lean_inc(v_toPure_2071_);
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2072_, 0, v_toPure_2071_);
lean_closure_set(v___f_2072_, 1, v_t_2067_);
lean_closure_set(v___f_2072_, 2, v_inst_2065_);
lean_closure_set(v___f_2072_, 3, v_inst_2066_);
v___x_2073_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v_getInfoState_2070_, v___f_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_t_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2075_, v_inst_2076_, v_t_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_info_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_info_2081_);
v___x_2083_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2079_, v_inst_2080_, v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_info_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2085_, v_inst_2086_, v_info_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2089_, lean_object* v_expectedType_x3f_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_____do__lift_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v_stx_2089_);
v___x_2096_ = l_Lean_LocalContext_empty;
v___x_2097_ = 0;
v___x_2098_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2098_, 0, v___x_2095_);
lean_ctor_set(v___x_2098_, 1, v___x_2096_);
lean_ctor_set(v___x_2098_, 2, v_expectedType_x3f_2090_);
lean_ctor_set(v___x_2098_, 3, v_____do__lift_2093_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*4, v___x_2097_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*4 + 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
v___x_2100_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2091_, v_inst_2092_, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_stx_2105_, lean_object* v_n_2106_, lean_object* v_expectedType_x3f_2107_){
_start:
{
lean_object* v_toBind_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toBind_2108_ = lean_ctor_get(v_inst_2101_, 1);
lean_inc(v_toBind_2108_);
lean_inc_ref(v_inst_2101_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2109_, 0, v_stx_2105_);
lean_closure_set(v___f_2109_, 1, v_expectedType_x3f_2107_);
lean_closure_set(v___f_2109_, 2, v_inst_2101_);
lean_closure_set(v___f_2109_, 3, v_inst_2102_);
v___x_2110_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2101_, v_inst_2103_, v_inst_2104_, v_n_2106_);
v___x_2111_ = lean_apply_4(v_toBind_2108_, lean_box(0), lean_box(0), v___x_2110_, v___f_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_stx_2117_, lean_object* v_n_2118_, lean_object* v_expectedType_x3f_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2113_, v_inst_2114_, v_inst_2115_, v_inst_2116_, v_stx_2117_, v_n_2118_, v_expectedType_x3f_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v_infoState_2125_; uint8_t v_enabled_2126_; 
v___x_2124_ = lean_st_ref_get(v___y_2122_);
v_infoState_2125_ = lean_ctor_get(v___x_2124_, 8);
lean_inc_ref(v_infoState_2125_);
lean_dec(v___x_2124_);
v_enabled_2126_ = lean_ctor_get_uint8(v_infoState_2125_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2125_);
if (v_enabled_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v_t_2121_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v_infoState_2130_; lean_object* v_env_2131_; lean_object* v_nextMacroScope_2132_; lean_object* v_ngen_2133_; lean_object* v_auxDeclNGen_2134_; lean_object* v_traceState_2135_; lean_object* v_cache_2136_; lean_object* v_recordedDeps_2137_; lean_object* v_messages_2138_; lean_object* v_snapshotTasks_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2161_; 
v___x_2129_ = lean_st_ref_take(v___y_2122_);
v_infoState_2130_ = lean_ctor_get(v___x_2129_, 8);
v_env_2131_ = lean_ctor_get(v___x_2129_, 0);
v_nextMacroScope_2132_ = lean_ctor_get(v___x_2129_, 1);
v_ngen_2133_ = lean_ctor_get(v___x_2129_, 2);
v_auxDeclNGen_2134_ = lean_ctor_get(v___x_2129_, 3);
v_traceState_2135_ = lean_ctor_get(v___x_2129_, 4);
v_cache_2136_ = lean_ctor_get(v___x_2129_, 5);
v_recordedDeps_2137_ = lean_ctor_get(v___x_2129_, 6);
v_messages_2138_ = lean_ctor_get(v___x_2129_, 7);
v_snapshotTasks_2139_ = lean_ctor_get(v___x_2129_, 9);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2141_ = v___x_2129_;
v_isShared_2142_ = v_isSharedCheck_2161_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snapshotTasks_2139_);
lean_inc(v_infoState_2130_);
lean_inc(v_messages_2138_);
lean_inc(v_recordedDeps_2137_);
lean_inc(v_cache_2136_);
lean_inc(v_traceState_2135_);
lean_inc(v_auxDeclNGen_2134_);
lean_inc(v_ngen_2133_);
lean_inc(v_nextMacroScope_2132_);
lean_inc(v_env_2131_);
lean_dec(v___x_2129_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2161_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint8_t v_enabled_2143_; lean_object* v_assignment_2144_; lean_object* v_lazyAssignment_2145_; lean_object* v_trees_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2160_; 
v_enabled_2143_ = lean_ctor_get_uint8(v_infoState_2130_, sizeof(void*)*3);
v_assignment_2144_ = lean_ctor_get(v_infoState_2130_, 0);
v_lazyAssignment_2145_ = lean_ctor_get(v_infoState_2130_, 1);
v_trees_2146_ = lean_ctor_get(v_infoState_2130_, 2);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_infoState_2130_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2148_ = v_infoState_2130_;
v_isShared_2149_ = v_isSharedCheck_2160_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_trees_2146_);
lean_inc(v_lazyAssignment_2145_);
lean_inc(v_assignment_2144_);
lean_dec(v_infoState_2130_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2160_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = l_Lean_PersistentArray_push___redArg(v_trees_2146_, v_t_2121_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 2, v___x_2151_);
v___x_2153_ = v___x_2148_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_assignment_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_lazyAssignment_2145_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v___x_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*3, v_enabled_2143_);
v___x_2153_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 8, v___x_2153_);
v___x_2155_ = v___x_2141_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_env_2131_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_nextMacroScope_2132_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_ngen_2133_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_auxDeclNGen_2134_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_traceState_2135_);
lean_ctor_set(v_reuseFailAlloc_2158_, 5, v_cache_2136_);
lean_ctor_set(v_reuseFailAlloc_2158_, 6, v_recordedDeps_2137_);
lean_ctor_set(v_reuseFailAlloc_2158_, 7, v_messages_2138_);
lean_ctor_set(v_reuseFailAlloc_2158_, 8, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2158_, 9, v_snapshotTasks_2139_);
v___x_2155_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_st_ref_put(v___y_2122_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2150_);
return v___x_2157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2162_, v___y_2163_);
lean_dec(v___y_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v_infoState_2171_; uint8_t v_enabled_2172_; 
v___x_2170_ = lean_st_ref_get(v___y_2168_);
v_infoState_2171_ = lean_ctor_get(v___x_2170_, 8);
lean_inc_ref(v_infoState_2171_);
lean_dec(v___x_2170_);
v_enabled_2172_ = lean_ctor_get_uint8(v_infoState_2171_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2171_);
if (v_enabled_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v_t_2166_);
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2175_ = lean_unsigned_to_nat(32u);
v___x_2176_ = lean_mk_empty_array_with_capacity(v___x_2175_);
lean_dec_ref(v___x_2176_);
v___x_2177_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_t_2166_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2178_, v___y_2168_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2184_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set(v___x_2190_, 3, v___x_2189_);
lean_ctor_set(v___x_2190_, 4, v___x_2188_);
lean_ctor_set(v___x_2190_, 5, v___x_2188_);
lean_ctor_set(v___x_2190_, 6, v___x_2188_);
lean_ctor_set(v___x_2190_, 7, v___x_2188_);
lean_ctor_set(v___x_2190_, 8, v___x_2188_);
lean_ctor_set(v___x_2190_, 9, v___x_2188_);
lean_ctor_set(v___x_2190_, 10, v___x_2188_);
lean_ctor_set(v___x_2190_, 11, v___x_2187_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_box(1);
v___x_2192_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
lean_ctor_set(v___x_2194_, 2, v___x_2191_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2200_ = l_Lean_stringToMessageData(v___x_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2216_, lean_object* v_declHint_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_env_2222_; uint8_t v___x_2223_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_st_ref_get(v___y_2218_);
v_env_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc_ref(v_env_2222_);
lean_dec(v___x_2221_);
v___x_2223_ = l_Lean_Name_isAnonymous(v_declHint_2217_);
if (v___x_2223_ == 0)
{
uint8_t v_isExporting_2224_; 
v_isExporting_2224_ = lean_ctor_get_uint8(v_env_2222_, sizeof(void*)*13);
if (v_isExporting_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_dec_ref(v_env_2222_);
lean_dec(v_declHint_2217_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_msg_2216_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
lean_inc_ref(v_env_2222_);
v___x_2226_ = l_Lean_Environment_setExporting(v_env_2222_, v___x_2223_);
lean_inc(v_declHint_2217_);
lean_inc_ref(v___x_2226_);
v___x_2227_ = l_Lean_Environment_contains(v___x_2226_, v_declHint_2217_, v_isExporting_2224_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_dec_ref(v___x_2226_);
lean_dec_ref(v_env_2222_);
lean_dec(v_declHint_2217_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_msg_2216_);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_c_2234_; lean_object* v___x_2235_; 
v___x_2229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2231_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2226_);
v___x_2232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2226_);
lean_ctor_set(v___x_2232_, 1, v___x_2229_);
lean_ctor_set(v___x_2232_, 2, v___x_2230_);
lean_ctor_set(v___x_2232_, 3, v___x_2231_);
lean_inc(v_declHint_2217_);
v___x_2233_ = l_Lean_MessageData_ofConstName(v_declHint_2217_, v___x_2223_);
v_c_2234_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2234_, 0, v___x_2232_);
lean_ctor_set(v_c_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2226_, v_declHint_2217_);
lean_dec_ref(v___x_2226_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_env_2222_);
lean_dec(v_declHint_2217_);
v___x_2236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v_c_2234_);
v___x_2238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_MessageData_note(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_msg_2216_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
else
{
lean_object* v_val_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2277_; 
v_val_2243_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2245_ = v___x_2235_;
v_isShared_2246_ = v_isSharedCheck_2277_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_val_2243_);
lean_dec(v___x_2235_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2277_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v_moduleNames_2248_; lean_object* v_mod_2249_; uint8_t v___x_2250_; 
v___x_2247_ = l_Lean_Environment_header(v_env_2222_);
lean_dec_ref(v_env_2222_);
v_moduleNames_2248_ = lean_ctor_get(v___x_2247_, 4);
lean_inc_ref(v_moduleNames_2248_);
lean_dec_ref(v___x_2247_);
v_mod_2249_ = lean_array_get(v___x_2220_, v_moduleNames_2248_, v_val_2243_);
lean_dec(v_val_2243_);
lean_dec_ref(v_moduleNames_2248_);
v___x_2250_ = l_Lean_isPrivateName(v_declHint_2217_);
lean_dec(v_declHint_2217_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_c_2234_);
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_MessageData_ofName(v_mod_2249_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_note(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_msg_2216_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2260_);
v___x_2262_ = v___x_2245_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_c_2234_);
v___x_2266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = l_Lean_MessageData_ofName(v_mod_2249_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_MessageData_note(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_msg_2216_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2273_);
v___x_2275_ = v___x_2245_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2278_; 
lean_dec_ref(v_env_2222_);
lean_dec(v_declHint_2217_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_msg_2216_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2279_, lean_object* v_declHint_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2279_, v_declHint_2280_, v___y_2281_);
lean_dec(v___y_2281_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2284_, lean_object* v_declHint_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2299_; 
v___x_2289_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2284_, v_declHint_2285_, v___y_2287_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2294_ = l_Lean_unknownIdentifierMessageTag;
v___x_2295_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_a_2290_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2295_);
v___x_2297_ = v___x_2292_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2300_, v_declHint_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v_toCold_2311_; lean_object* v_env_2312_; lean_object* v_options_2313_; uint8_t v___x_2314_; lean_object* v_env_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2310_ = lean_st_ref_get(v___y_2308_);
v_toCold_2311_ = lean_ctor_get(v___y_2307_, 0);
v_env_2312_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_ref(v_env_2312_);
lean_dec(v___x_2310_);
v_options_2313_ = lean_ctor_get(v_toCold_2311_, 2);
v___x_2314_ = 0;
v_env_2315_ = l_Lean_Environment_setRecordingDeps(v_env_2312_, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2317_ = lean_unsigned_to_nat(32u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
lean_dec_ref(v___x_2318_);
v___x_2319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2313_);
v___x_2320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2320_, 0, v_env_2315_);
lean_ctor_set(v___x_2320_, 1, v___x_2316_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
lean_ctor_set(v___x_2320_, 3, v_options_2313_);
v___x_2321_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v_msgData_2306_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_ref_2332_; lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
v_ref_2332_ = lean_ctor_get(v___y_2329_, 2);
v___x_2333_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2328_, v___y_2329_, v___y_2330_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_inc(v_ref_2332_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_ref_2332_);
lean_ctor_set(v___x_2338_, 1, v_a_2334_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_toCold_2353_; lean_object* v_currRecDepth_2354_; lean_object* v_ref_2355_; uint16_t v_optionFlags_2356_; uint8_t v_suppressElabErrors_2357_; uint8_t v_checkDeprecated_2358_; uint8_t v_isRecordingDeps_2359_; lean_object* v_ref_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_toCold_2353_ = lean_ctor_get(v___y_2350_, 0);
v_currRecDepth_2354_ = lean_ctor_get(v___y_2350_, 1);
v_ref_2355_ = lean_ctor_get(v___y_2350_, 2);
v_optionFlags_2356_ = lean_ctor_get_uint16(v___y_2350_, sizeof(void*)*3);
v_suppressElabErrors_2357_ = lean_ctor_get_uint8(v___y_2350_, sizeof(void*)*3 + 2);
v_checkDeprecated_2358_ = lean_ctor_get_uint8(v___y_2350_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2359_ = lean_ctor_get_uint8(v___y_2350_, sizeof(void*)*3 + 4);
v_ref_2360_ = l_Lean_replaceRef(v_ref_2348_, v_ref_2355_);
lean_inc(v_currRecDepth_2354_);
lean_inc_ref(v_toCold_2353_);
v___x_2361_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2361_, 0, v_toCold_2353_);
lean_ctor_set(v___x_2361_, 1, v_currRecDepth_2354_);
lean_ctor_set(v___x_2361_, 2, v_ref_2360_);
lean_ctor_set_uint16(v___x_2361_, sizeof(void*)*3, v_optionFlags_2356_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*3 + 2, v_suppressElabErrors_2357_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*3 + 3, v_checkDeprecated_2358_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*3 + 4, v_isRecordingDeps_2359_);
v___x_2362_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2349_, v___x_2361_, v___y_2351_);
lean_dec_ref_known(v___x_2361_, 3);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2363_, lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2363_, v_msg_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v_ref_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2369_, lean_object* v_msg_2370_, lean_object* v_declHint_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v___x_2377_; 
v___x_2375_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2370_, v_declHint_2371_, v___y_2372_, v___y_2373_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2369_, v_a_2376_, v___y_2372_, v___y_2373_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2378_, lean_object* v_msg_2379_, lean_object* v_declHint_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2378_, v_msg_2379_, v_declHint_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v_ref_2378_);
return v_res_2384_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2391_, lean_object* v_constName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2396_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2397_ = 0;
lean_inc(v_constName_2392_);
v___x_2398_ = l_Lean_MessageData_ofConstName(v_constName_2392_, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2391_, v___x_2401_, v_constName_2392_, v___y_2393_, v___y_2394_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2403_, lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2403_, v_constName_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_ref_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_ref_2413_; lean_object* v___x_2414_; 
v_ref_2413_ = lean_ctor_get(v___y_2410_, 2);
v___x_2414_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2413_, v_constName_2409_, v___y_2410_, v___y_2411_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v_env_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2424_ = lean_st_ref_get(v___y_2422_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc_ref(v_env_2425_);
lean_dec(v___x_2424_);
v___x_2426_ = 0;
lean_inc(v_constName_2420_);
v___x_2427_ = l_Lean_Environment_findConstVal_x3f(v_env_2425_, v_constName_2420_, v___x_2426_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2420_, v___y_2421_, v___y_2422_);
return v___x_2428_;
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_constName_2420_);
v_val_2429_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2427_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_val_2429_);
lean_dec(v___x_2427_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 0);
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_val_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
if (lean_obj_tag(v_a_2442_) == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = l_List_reverse___redArg(v_a_2443_);
return v___x_2444_;
}
else
{
lean_object* v_head_2445_; lean_object* v_tail_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
v_head_2445_ = lean_ctor_get(v_a_2442_, 0);
v_tail_2446_ = lean_ctor_get(v_a_2442_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v_a_2442_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_tail_2446_);
lean_inc(v_head_2445_);
lean_dec(v_a_2442_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = l_Lean_mkLevelParam(v_head_2445_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v_a_2443_);
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_a_2443_);
v___x_2452_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
v_a_2442_ = v_tail_2446_;
v_a_2443_ = v___x_2452_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
lean_inc(v_constName_2456_);
v___x_2460_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2472_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2472_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2472_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v_levelParams_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v_levelParams_2465_ = lean_ctor_get(v_a_2461_, 1);
lean_inc(v_levelParams_2465_);
lean_dec(v_a_2461_);
v___x_2466_ = lean_box(0);
v___x_2467_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2465_, v___x_2466_);
v___x_2468_ = l_Lean_mkConst(v_constName_2456_, v___x_2467_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2468_);
v___x_2470_ = v___x_2463_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_constName_2456_);
v_a_2473_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2460_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2460_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2486_, lean_object* v_n_2487_, lean_object* v_expectedType_x3f_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2487_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v_stx_2486_);
v___x_2496_ = l_Lean_LocalContext_empty;
v___x_2497_ = 0;
v___x_2498_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2498_, 0, v___x_2495_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
lean_ctor_set(v___x_2498_, 2, v_expectedType_x3f_2488_);
lean_ctor_set(v___x_2498_, 3, v_a_2493_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*4, v___x_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*4 + 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
v___x_2500_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2499_, v___y_2489_, v___y_2490_);
return v___x_2500_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_expectedType_x3f_2488_);
lean_dec(v_stx_2486_);
v_a_2501_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2492_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2492_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2509_, lean_object* v_n_2510_, lean_object* v_expectedType_x3f_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2509_, v_n_2510_, v_expectedType_x3f_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2516_, lean_object* v_expectedType_x3f_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
lean_inc(v_id_2516_);
v___x_2521_ = l_Lean_realizeGlobalConstNoOverload(v_id_2516_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2549_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2549_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2549_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v_infoState_2527_; uint8_t v_enabled_2528_; 
v___x_2526_ = lean_st_ref_get(v_a_2519_);
v_infoState_2527_ = lean_ctor_get(v___x_2526_, 8);
lean_inc_ref(v_infoState_2527_);
lean_dec(v___x_2526_);
v_enabled_2528_ = lean_ctor_get_uint8(v_infoState_2527_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2527_);
if (v_enabled_2528_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_expectedType_x3f_2517_);
lean_dec(v_id_2516_);
if (v_isShared_2525_ == 0)
{
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2522_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; 
lean_del_object(v___x_2524_);
lean_inc(v_a_2522_);
v___x_2532_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2516_, v_a_2522_, v_expectedType_x3f_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2532_, 0);
lean_dec(v_unused_2540_);
v___x_2534_ = v___x_2532_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_dec(v___x_2532_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v_a_2522_);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2522_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2522_);
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2517_);
lean_dec(v_id_2516_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2550_, lean_object* v_expectedType_x3f_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2550_, v_expectedType_x3f_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2556_, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2566_, lean_object* v_constName_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2567_, v___y_2568_, v___y_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2572_, lean_object* v_constName_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2572_, v_constName_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2578_, lean_object* v_ref_2579_, lean_object* v_constName_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2579_, v_constName_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2585_, lean_object* v_ref_2586_, lean_object* v_constName_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2585_, v_ref_2586_, v_constName_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v_ref_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2592_, lean_object* v_ref_2593_, lean_object* v_msg_2594_, lean_object* v_declHint_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2593_, v_msg_2594_, v_declHint_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2600_, lean_object* v_ref_2601_, lean_object* v_msg_2602_, lean_object* v_declHint_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2600_, v_ref_2601_, v_msg_2602_, v_declHint_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v_ref_2601_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2608_, lean_object* v_declHint_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2608_, v_declHint_2609_, v___y_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2614_, lean_object* v_declHint_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2614_, v_declHint_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2620_, lean_object* v_ref_2621_, lean_object* v_msg_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2621_, v_msg_2622_, v___y_2623_, v___y_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_ref_2628_, lean_object* v_msg_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2627_, v_ref_2628_, v_msg_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v_ref_2628_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2634_, lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_msg_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2640_, v_msg_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2646_, lean_object* v_expectedType_x3f_2647_, lean_object* v_as_x27_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
if (lean_obj_tag(v_as_x27_2648_) == 0)
{
lean_object* v___x_2653_; 
lean_dec(v_expectedType_x3f_2647_);
lean_dec(v_id_2646_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_b_2649_);
return v___x_2653_;
}
else
{
lean_object* v_head_2654_; lean_object* v_tail_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_head_2654_ = lean_ctor_get(v_as_x27_2648_, 0);
v_tail_2655_ = lean_ctor_get(v_as_x27_2648_, 1);
v___x_2656_ = lean_box(0);
lean_inc(v_expectedType_x3f_2647_);
lean_inc(v_head_2654_);
lean_inc(v_id_2646_);
v___x_2657_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2646_, v_head_2654_, v_expectedType_x3f_2647_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref_known(v___x_2657_, 1);
v_as_x27_2648_ = v_tail_2655_;
v_b_2649_ = v___x_2656_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2647_);
lean_dec(v_id_2646_);
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2659_, lean_object* v_expectedType_x3f_2660_, lean_object* v_as_x27_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2659_, v_expectedType_x3f_2660_, v_as_x27_2661_, v_b_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v_as_x27_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2667_, lean_object* v_expectedType_x3f_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2672_; 
lean_inc(v_id_2667_);
v___x_2672_ = l_Lean_realizeGlobalConst(v_id_2667_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2701_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v_infoState_2678_; uint8_t v_enabled_2679_; 
v___x_2677_ = lean_st_ref_get(v_a_2670_);
v_infoState_2678_ = lean_ctor_get(v___x_2677_, 8);
lean_inc_ref(v_infoState_2678_);
lean_dec(v___x_2677_);
v_enabled_2679_ = lean_ctor_get_uint8(v_infoState_2678_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2678_);
if (v_enabled_2679_ == 0)
{
lean_object* v___x_2681_; 
lean_dec(v_expectedType_x3f_2668_);
lean_dec(v_id_2667_);
if (v_isShared_2676_ == 0)
{
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2673_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_del_object(v___x_2675_);
v___x_2683_ = lean_box(0);
v___x_2684_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2667_, v_expectedType_x3f_2668_, v_a_2673_, v___x_2683_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2692_);
v___x_2686_ = v___x_2684_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v___x_2684_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_a_2673_);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2673_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_a_2673_);
v_a_2693_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2684_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2684_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2668_);
lean_dec(v_id_2667_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2702_, lean_object* v_expectedType_x3f_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2702_, v_expectedType_x3f_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2708_, lean_object* v_expectedType_x3f_2709_, lean_object* v_as_2710_, lean_object* v_as_x27_2711_, lean_object* v_b_2712_, lean_object* v_a_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2708_, v_expectedType_x3f_2709_, v_as_x27_2711_, v_b_2712_, v___y_2714_, v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2718_, lean_object* v_expectedType_x3f_2719_, lean_object* v_as_2720_, lean_object* v_as_x27_2721_, lean_object* v_b_2722_, lean_object* v_a_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2718_, v_expectedType_x3f_2719_, v_as_2720_, v_as_x27_2721_, v_b_2722_, v_a_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_as_x27_2721_);
lean_dec(v_as_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2728_, lean_object* v_as_x27_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
if (lean_obj_tag(v_as_x27_2729_) == 0)
{
lean_object* v___x_2734_; 
lean_dec(v_ref_2728_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_b_2730_);
return v___x_2734_;
}
else
{
lean_object* v_head_2735_; lean_object* v_tail_2736_; lean_object* v_fst_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_head_2735_ = lean_ctor_get(v_as_x27_2729_, 0);
v_tail_2736_ = lean_ctor_get(v_as_x27_2729_, 1);
v_fst_2737_ = lean_ctor_get(v_head_2735_, 0);
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_box(0);
lean_inc(v_fst_2737_);
lean_inc(v_ref_2728_);
v___x_2740_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2728_, v_fst_2737_, v___x_2739_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_dec_ref_known(v___x_2740_, 1);
v_as_x27_2729_ = v_tail_2736_;
v_b_2730_ = v___x_2738_;
goto _start;
}
else
{
lean_dec(v_ref_2728_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2742_, lean_object* v_as_x27_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2742_, v_as_x27_2743_, v_b_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v_as_x27_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2749_, lean_object* v_id_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_realizeGlobalName(v_id_2750_, v_a_2751_, v_a_2752_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2783_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2783_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2783_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v_infoState_2760_; uint8_t v_enabled_2761_; 
v___x_2759_ = lean_st_ref_get(v_a_2752_);
v_infoState_2760_ = lean_ctor_get(v___x_2759_, 8);
lean_inc_ref(v_infoState_2760_);
lean_dec(v___x_2759_);
v_enabled_2761_ = lean_ctor_get_uint8(v_infoState_2760_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2760_);
if (v_enabled_2761_ == 0)
{
lean_object* v___x_2763_; 
lean_dec(v_ref_2749_);
if (v_isShared_2758_ == 0)
{
v___x_2763_ = v___x_2757_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2755_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_del_object(v___x_2757_);
v___x_2765_ = lean_box(0);
v___x_2766_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2749_, v_a_2755_, v___x_2765_, v_a_2751_, v_a_2752_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v___x_2766_, 0);
lean_dec(v_unused_2774_);
v___x_2768_ = v___x_2766_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v___x_2766_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v_a_2755_);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2755_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2755_);
v_a_2775_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2766_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2766_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2749_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2784_, lean_object* v_id_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2784_, v_id_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2790_, lean_object* v_as_2791_, lean_object* v_as_x27_2792_, lean_object* v_b_2793_, lean_object* v_a_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2790_, v_as_x27_2792_, v_b_2793_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2799_, lean_object* v_as_2800_, lean_object* v_as_x27_2801_, lean_object* v_b_2802_, lean_object* v_a_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2799_, v_as_2800_, v_as_x27_2801_, v_b_2802_, v_a_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_as_x27_2801_);
lean_dec(v_as_2800_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2808_){
_start:
{
lean_object* v_fst_2809_; 
v_fst_2809_ = lean_ctor_get(v_self_2808_, 0);
lean_inc(v_fst_2809_);
return v_fst_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2810_);
lean_dec_ref(v_self_2810_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2812_, lean_object* v_treesSaved_2813_, lean_object* v_s_2814_){
_start:
{
if (lean_obj_tag(v_info_2812_) == 0)
{
uint8_t v_enabled_2815_; lean_object* v_assignment_2816_; lean_object* v_lazyAssignment_2817_; lean_object* v_trees_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2828_; 
v_enabled_2815_ = lean_ctor_get_uint8(v_s_2814_, sizeof(void*)*3);
v_assignment_2816_ = lean_ctor_get(v_s_2814_, 0);
v_lazyAssignment_2817_ = lean_ctor_get(v_s_2814_, 1);
v_trees_2818_ = lean_ctor_get(v_s_2814_, 2);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_s_2814_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2820_ = v_s_2814_;
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_trees_2818_);
lean_inc(v_lazyAssignment_2817_);
lean_inc(v_assignment_2816_);
lean_dec(v_s_2814_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v_val_2822_ = lean_ctor_get(v_info_2812_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v_info_2812_, 1);
v___x_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_val_2822_);
lean_ctor_set(v___x_2823_, 1, v_trees_2818_);
v___x_2824_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2813_, v___x_2823_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 2, v___x_2824_);
v___x_2826_ = v___x_2820_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_assignment_2816_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_lazyAssignment_2817_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v___x_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*3, v_enabled_2815_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
uint8_t v_enabled_2829_; lean_object* v_assignment_2830_; lean_object* v_lazyAssignment_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2847_; 
v_enabled_2829_ = lean_ctor_get_uint8(v_s_2814_, sizeof(void*)*3);
v_assignment_2830_ = lean_ctor_get(v_s_2814_, 0);
v_lazyAssignment_2831_ = lean_ctor_get(v_s_2814_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_s_2814_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_s_2814_, 2);
lean_dec(v_unused_2848_);
v___x_2833_ = v_s_2814_;
v_isShared_2834_ = v_isSharedCheck_2847_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_lazyAssignment_2831_);
lean_inc(v_assignment_2830_);
lean_dec(v_s_2814_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2847_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v_val_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v_val_2835_ = lean_ctor_get(v_info_2812_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_info_2812_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2837_ = v_info_2812_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_val_2835_);
lean_dec(v_info_2812_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 2);
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_val_2835_);
v___x_2840_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2841_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2813_, v___x_2840_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 2, v___x_2841_);
v___x_2843_ = v___x_2833_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_assignment_2830_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_lazyAssignment_2831_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v___x_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2844_, sizeof(void*)*3, v_enabled_2829_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2849_, lean_object* v_modifyInfoState_2850_, lean_object* v_info_2851_){
_start:
{
lean_object* v___f_2852_; lean_object* v___x_2853_; 
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2852_, 0, v_info_2851_);
lean_closure_set(v___f_2852_, 1, v_treesSaved_2849_);
v___x_2853_ = lean_apply_1(v_modifyInfoState_2850_, v___f_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2854_, lean_object* v_info_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_apply_1(v___f_2854_, v_info_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2857_, lean_object* v_toBind_2858_, lean_object* v___f_2859_, lean_object* v_____do__lift_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_____do__lift_2860_);
v___x_2862_ = lean_apply_2(v_toPure_2857_, lean_box(0), v___x_2861_);
v___x_2863_ = lean_apply_4(v_toBind_2858_, lean_box(0), lean_box(0), v___x_2862_, v___f_2859_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2864_, lean_object* v_mkInfoOnError_2865_, lean_object* v___f_2866_, lean_object* v_mkInfo_2867_, lean_object* v___f_2868_, lean_object* v_a_x3f_2869_){
_start:
{
if (lean_obj_tag(v_a_x3f_2869_) == 0)
{
lean_object* v___x_2870_; 
lean_dec(v___f_2868_);
lean_dec(v_mkInfo_2867_);
v___x_2870_ = lean_apply_4(v_toBind_2864_, lean_box(0), lean_box(0), v_mkInfoOnError_2865_, v___f_2866_);
return v___x_2870_;
}
else
{
lean_object* v_val_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v___f_2866_);
lean_dec(v_mkInfoOnError_2865_);
v_val_2871_ = lean_ctor_get(v_a_x3f_2869_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_a_x3f_2869_, 1);
v___x_2872_ = lean_apply_1(v_mkInfo_2867_, v_val_2871_);
v___x_2873_ = lean_apply_4(v_toBind_2864_, lean_box(0), lean_box(0), v___x_2872_, v___f_2868_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2874_, lean_object* v_modifyInfoState_2875_, lean_object* v_toPure_2876_, lean_object* v_toBind_2877_, lean_object* v_mkInfoOnError_2878_, lean_object* v_mkInfo_2879_, lean_object* v_inst_2880_, lean_object* v_x_2881_, lean_object* v___f_2882_, lean_object* v_treesSaved_2883_){
_start:
{
lean_object* v_map_2884_; lean_object* v___f_2885_; lean_object* v___f_2886_; lean_object* v___f_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_map_2884_ = lean_ctor_get(v_toFunctor_2874_, 0);
lean_inc(v_map_2884_);
lean_dec_ref(v_toFunctor_2874_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2885_, 0, v_treesSaved_2883_);
lean_closure_set(v___f_2885_, 1, v_modifyInfoState_2875_);
v___f_2886_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2886_, 0, v___f_2885_);
lean_inc_ref(v___f_2886_);
lean_inc(v_toBind_2877_);
v___f_2887_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2887_, 0, v_toPure_2876_);
lean_closure_set(v___f_2887_, 1, v_toBind_2877_);
lean_closure_set(v___f_2887_, 2, v___f_2886_);
v___f_2888_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2888_, 0, v_toBind_2877_);
lean_closure_set(v___f_2888_, 1, v_mkInfoOnError_2878_);
lean_closure_set(v___f_2888_, 2, v___f_2887_);
lean_closure_set(v___f_2888_, 3, v_mkInfo_2879_);
lean_closure_set(v___f_2888_, 4, v___f_2886_);
v___x_2889_ = lean_apply_4(v_inst_2880_, lean_box(0), lean_box(0), v_x_2881_, v___f_2888_);
v___x_2890_ = lean_apply_4(v_map_2884_, lean_box(0), lean_box(0), v___f_2882_, v___x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_toBind_2894_, lean_object* v___f_2895_, lean_object* v_____do__lift_2896_){
_start:
{
uint8_t v_enabled_2897_; 
v_enabled_2897_ = lean_ctor_get_uint8(v_____do__lift_2896_, sizeof(void*)*3);
if (v_enabled_2897_ == 0)
{
lean_dec(v___f_2895_);
lean_dec(v_toBind_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec_ref(v_inst_2892_);
lean_inc(v_x_2891_);
return v_x_2891_;
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2892_, v_inst_2893_);
v___x_2899_ = lean_apply_4(v_toBind_2894_, lean_box(0), lean_box(0), v___x_2898_, v___f_2895_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2900_, lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_toBind_2903_, lean_object* v___f_2904_, lean_object* v_____do__lift_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2900_, v_inst_2901_, v_inst_2902_, v_toBind_2903_, v___f_2904_, v_____do__lift_2905_);
lean_dec_ref(v_____do__lift_2905_);
lean_dec(v_x_2900_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_x_2911_, lean_object* v_mkInfo_2912_, lean_object* v_mkInfoOnError_2913_){
_start:
{
lean_object* v_toApplicative_2914_; lean_object* v_toBind_2915_; lean_object* v_getInfoState_2916_; lean_object* v_modifyInfoState_2917_; lean_object* v_toFunctor_2918_; lean_object* v_toPure_2919_; lean_object* v___f_2920_; lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; 
v_toApplicative_2914_ = lean_ctor_get(v_inst_2908_, 0);
v_toBind_2915_ = lean_ctor_get(v_inst_2908_, 1);
lean_inc_n(v_toBind_2915_, 3);
v_getInfoState_2916_ = lean_ctor_get(v_inst_2909_, 0);
lean_inc(v_getInfoState_2916_);
v_modifyInfoState_2917_ = lean_ctor_get(v_inst_2909_, 1);
v_toFunctor_2918_ = lean_ctor_get(v_toApplicative_2914_, 0);
v_toPure_2919_ = lean_ctor_get(v_toApplicative_2914_, 1);
v___f_2920_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2911_);
lean_inc(v_toPure_2919_);
lean_inc(v_modifyInfoState_2917_);
lean_inc_ref(v_toFunctor_2918_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2921_, 0, v_toFunctor_2918_);
lean_closure_set(v___f_2921_, 1, v_modifyInfoState_2917_);
lean_closure_set(v___f_2921_, 2, v_toPure_2919_);
lean_closure_set(v___f_2921_, 3, v_toBind_2915_);
lean_closure_set(v___f_2921_, 4, v_mkInfoOnError_2913_);
lean_closure_set(v___f_2921_, 5, v_mkInfo_2912_);
lean_closure_set(v___f_2921_, 6, v_inst_2910_);
lean_closure_set(v___f_2921_, 7, v_x_2911_);
lean_closure_set(v___f_2921_, 8, v___f_2920_);
v___f_2922_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2922_, 0, v_x_2911_);
lean_closure_set(v___f_2922_, 1, v_inst_2908_);
lean_closure_set(v___f_2922_, 2, v_inst_2909_);
lean_closure_set(v___f_2922_, 3, v_toBind_2915_);
lean_closure_set(v___f_2922_, 4, v___f_2921_);
v___x_2923_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v_getInfoState_2916_, v___f_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_00_u03b1_2927_, lean_object* v_inst_2928_, lean_object* v_x_2929_, lean_object* v_mkInfo_2930_, lean_object* v_mkInfoOnError_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2925_, v_inst_2926_, v_inst_2928_, v_x_2929_, v_mkInfo_2930_, v_mkInfoOnError_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2933_, lean_object* v_tree_2934_, lean_object* v_s_2935_){
_start:
{
uint8_t v_enabled_2936_; lean_object* v_assignment_2937_; lean_object* v_lazyAssignment_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2946_; 
v_enabled_2936_ = lean_ctor_get_uint8(v_s_2935_, sizeof(void*)*3);
v_assignment_2937_ = lean_ctor_get(v_s_2935_, 0);
v_lazyAssignment_2938_ = lean_ctor_get(v_s_2935_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_s_2935_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v_s_2935_, 2);
lean_dec(v_unused_2947_);
v___x_2940_ = v_s_2935_;
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_lazyAssignment_2938_);
lean_inc(v_assignment_2937_);
lean_dec(v_s_2935_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2933_, v_tree_2934_);
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
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_assignment_2937_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_lazyAssignment_2938_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v___x_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2945_, sizeof(void*)*3, v_enabled_2936_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2948_, lean_object* v_modifyInfoState_2949_, lean_object* v_tree_2950_){
_start:
{
lean_object* v___f_2951_; lean_object* v___x_2952_; 
v___f_2951_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2951_, 0, v_treesSaved_2948_);
lean_closure_set(v___f_2951_, 1, v_tree_2950_);
v___x_2952_ = lean_apply_1(v_modifyInfoState_2949_, v___f_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2953_, lean_object* v_toBind_2954_, lean_object* v___f_2955_, lean_object* v_st_2956_){
_start:
{
lean_object* v_trees_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_trees_2957_ = lean_ctor_get(v_st_2956_, 2);
lean_inc_ref(v_trees_2957_);
lean_dec_ref(v_st_2956_);
v___x_2958_ = lean_apply_1(v_mkInfoTree_2953_, v_trees_2957_);
v___x_2959_ = lean_apply_4(v_toBind_2954_, lean_box(0), lean_box(0), v___x_2958_, v___f_2955_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2960_, lean_object* v_getInfoState_2961_, lean_object* v___f_2962_, lean_object* v_x_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_apply_4(v_toBind_2960_, lean_box(0), lean_box(0), v_getInfoState_2961_, v___f_2962_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2965_, lean_object* v_getInfoState_2966_, lean_object* v___f_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2965_, v_getInfoState_2966_, v___f_2967_, v_x_2968_);
lean_dec(v_x_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2970_, lean_object* v_modifyInfoState_2971_, lean_object* v_mkInfoTree_2972_, lean_object* v_toBind_2973_, lean_object* v_getInfoState_2974_, lean_object* v_inst_2975_, lean_object* v_x_2976_, lean_object* v___f_2977_, lean_object* v_treesSaved_2978_){
_start:
{
lean_object* v_map_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_map_2979_ = lean_ctor_get(v_toFunctor_2970_, 0);
lean_inc(v_map_2979_);
lean_dec_ref(v_toFunctor_2970_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2980_, 0, v_treesSaved_2978_);
lean_closure_set(v___f_2980_, 1, v_modifyInfoState_2971_);
lean_inc(v_toBind_2973_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2981_, 0, v_mkInfoTree_2972_);
lean_closure_set(v___f_2981_, 1, v_toBind_2973_);
lean_closure_set(v___f_2981_, 2, v___f_2980_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2982_, 0, v_toBind_2973_);
lean_closure_set(v___f_2982_, 1, v_getInfoState_2974_);
lean_closure_set(v___f_2982_, 2, v___f_2981_);
v___x_2983_ = lean_apply_4(v_inst_2975_, lean_box(0), lean_box(0), v_x_2976_, v___f_2982_);
v___x_2984_ = lean_apply_4(v_map_2979_, lean_box(0), lean_box(0), v___f_2977_, v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_x_2988_, lean_object* v_mkInfoTree_2989_){
_start:
{
lean_object* v_toApplicative_2990_; lean_object* v_toBind_2991_; lean_object* v_getInfoState_2992_; lean_object* v_modifyInfoState_2993_; lean_object* v_toFunctor_2994_; lean_object* v___f_2995_; lean_object* v___f_2996_; lean_object* v___f_2997_; lean_object* v___x_2998_; 
v_toApplicative_2990_ = lean_ctor_get(v_inst_2985_, 0);
v_toBind_2991_ = lean_ctor_get(v_inst_2985_, 1);
lean_inc_n(v_toBind_2991_, 3);
v_getInfoState_2992_ = lean_ctor_get(v_inst_2986_, 0);
lean_inc_n(v_getInfoState_2992_, 2);
v_modifyInfoState_2993_ = lean_ctor_get(v_inst_2986_, 1);
v_toFunctor_2994_ = lean_ctor_get(v_toApplicative_2990_, 0);
v___f_2995_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2988_);
lean_inc(v_modifyInfoState_2993_);
lean_inc_ref(v_toFunctor_2994_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2996_, 0, v_toFunctor_2994_);
lean_closure_set(v___f_2996_, 1, v_modifyInfoState_2993_);
lean_closure_set(v___f_2996_, 2, v_mkInfoTree_2989_);
lean_closure_set(v___f_2996_, 3, v_toBind_2991_);
lean_closure_set(v___f_2996_, 4, v_getInfoState_2992_);
lean_closure_set(v___f_2996_, 5, v_inst_2987_);
lean_closure_set(v___f_2996_, 6, v_x_2988_);
lean_closure_set(v___f_2996_, 7, v___f_2995_);
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2997_, 0, v_x_2988_);
lean_closure_set(v___f_2997_, 1, v_inst_2985_);
lean_closure_set(v___f_2997_, 2, v_inst_2986_);
lean_closure_set(v___f_2997_, 3, v_toBind_2991_);
lean_closure_set(v___f_2997_, 4, v___f_2996_);
v___x_2998_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v_getInfoState_2992_, v___f_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_00_u03b1_3002_, lean_object* v_inst_3003_, lean_object* v_x_3004_, lean_object* v_mkInfoTree_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3000_, v_inst_3001_, v_inst_3003_, v_x_3004_, v_mkInfoTree_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3007_, lean_object* v_toPure_3008_, lean_object* v_____do__lift_3009_){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_____do__lift_3009_);
lean_ctor_set(v___x_3010_, 1, v_trees_3007_);
v___x_3011_ = lean_apply_2(v_toPure_3008_, lean_box(0), v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3012_, lean_object* v_toBind_3013_, lean_object* v_mkInfo_3014_, lean_object* v_trees_3015_){
_start:
{
lean_object* v___f_3016_; lean_object* v___x_3017_; 
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3016_, 0, v_trees_3015_);
lean_closure_set(v___f_3016_, 1, v_toPure_3012_);
v___x_3017_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v_mkInfo_3014_, v___f_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_x_3021_, lean_object* v_mkInfo_3022_){
_start:
{
lean_object* v_toApplicative_3023_; lean_object* v_toBind_3024_; lean_object* v_toPure_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; 
v_toApplicative_3023_ = lean_ctor_get(v_inst_3018_, 0);
v_toBind_3024_ = lean_ctor_get(v_inst_3018_, 1);
v_toPure_3025_ = lean_ctor_get(v_toApplicative_3023_, 1);
lean_inc(v_toBind_3024_);
lean_inc(v_toPure_3025_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3026_, 0, v_toPure_3025_);
lean_closure_set(v___f_3026_, 1, v_toBind_3024_);
lean_closure_set(v___f_3026_, 2, v_mkInfo_3022_);
v___x_3027_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3018_, v_inst_3019_, v_inst_3020_, v_x_3021_, v___f_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_00_u03b1_3031_, lean_object* v_inst_3032_, lean_object* v_x_3033_, lean_object* v_mkInfo_3034_){
_start:
{
lean_object* v_toApplicative_3035_; lean_object* v_toBind_3036_; lean_object* v_toPure_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; 
v_toApplicative_3035_ = lean_ctor_get(v_inst_3029_, 0);
v_toBind_3036_ = lean_ctor_get(v_inst_3029_, 1);
v_toPure_3037_ = lean_ctor_get(v_toApplicative_3035_, 1);
lean_inc(v_toBind_3036_);
lean_inc(v_toPure_3037_);
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3038_, 0, v_toPure_3037_);
lean_closure_set(v___f_3038_, 1, v_toBind_3036_);
lean_closure_set(v___f_3038_, 2, v_mkInfo_3034_);
v___x_3039_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3029_, v_inst_3030_, v_inst_3032_, v_x_3033_, v___f_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3040_, lean_object* v_trees_3041_, lean_object* v_s_3042_){
_start:
{
uint8_t v_enabled_3043_; lean_object* v_assignment_3044_; lean_object* v_lazyAssignment_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3053_; 
v_enabled_3043_ = lean_ctor_get_uint8(v_s_3042_, sizeof(void*)*3);
v_assignment_3044_ = lean_ctor_get(v_s_3042_, 0);
v_lazyAssignment_3045_ = lean_ctor_get(v_s_3042_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_s_3042_);
if (v_isSharedCheck_3053_ == 0)
{
lean_object* v_unused_3054_; 
v_unused_3054_ = lean_ctor_get(v_s_3042_, 2);
lean_dec(v_unused_3054_);
v___x_3047_ = v_s_3042_;
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_lazyAssignment_3045_);
lean_inc(v_assignment_3044_);
lean_dec(v_s_3042_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3040_, v_trees_3041_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 2, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_assignment_3044_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_lazyAssignment_3045_);
lean_ctor_set(v_reuseFailAlloc_3052_, 2, v___x_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, sizeof(void*)*3, v_enabled_3043_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3055_, lean_object* v_trees_3056_, lean_object* v_s_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3055_, v_trees_3056_, v_s_3057_);
lean_dec_ref(v_trees_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3059_, lean_object* v_modifyInfoState_3060_, lean_object* v_trees_3061_){
_start:
{
lean_object* v___f_3062_; lean_object* v___x_3063_; 
v___f_3062_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3062_, 0, v_treesSaved_3059_);
lean_closure_set(v___f_3062_, 1, v_trees_3061_);
v___x_3063_ = lean_apply_1(v_modifyInfoState_3060_, v___f_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3064_, lean_object* v_tree_3065_, lean_object* v_____do__lift_3066_){
_start:
{
if (lean_obj_tag(v_____do__lift_3066_) == 0)
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_apply_2(v_toPure_3064_, lean_box(0), v_tree_3065_);
return v___x_3067_;
}
else
{
lean_object* v_val_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_val_3068_ = lean_ctor_get(v_____do__lift_3066_, 0);
lean_inc(v_val_3068_);
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_val_3068_);
lean_ctor_set(v___x_3069_, 1, v_tree_3065_);
v___x_3070_ = lean_apply_2(v_toPure_3064_, lean_box(0), v___x_3069_);
return v___x_3070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3071_, lean_object* v_tree_3072_, lean_object* v_____do__lift_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3071_, v_tree_3072_, v_____do__lift_3073_);
lean_dec(v_____do__lift_3073_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3075_, lean_object* v_toPure_3076_, lean_object* v_toBind_3077_, lean_object* v_ctx_x3f_3078_, lean_object* v_tree_3079_){
_start:
{
lean_object* v_tree_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; 
v_tree_3080_ = l_Lean_Elab_InfoTree_substitute(v_tree_3079_, v_assignment_3075_);
v___f_3081_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3081_, 0, v_toPure_3076_);
lean_closure_set(v___f_3081_, 1, v_tree_3080_);
v___x_3082_ = lean_apply_4(v_toBind_3077_, lean_box(0), lean_box(0), v_ctx_x3f_3078_, v___f_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3083_, lean_object* v_toPure_3084_, lean_object* v_toBind_3085_, lean_object* v_ctx_x3f_3086_, lean_object* v_tree_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3083_, v_toPure_3084_, v_toBind_3085_, v_ctx_x3f_3086_, v_tree_3087_);
lean_dec_ref(v_assignment_3083_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3089_, lean_object* v_toBind_3090_, lean_object* v_ctx_x3f_3091_, lean_object* v_inst_3092_, lean_object* v___f_3093_, lean_object* v_st_3094_){
_start:
{
lean_object* v_assignment_3095_; lean_object* v_trees_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_assignment_3095_ = lean_ctor_get(v_st_3094_, 0);
lean_inc_ref(v_assignment_3095_);
v_trees_3096_ = lean_ctor_get(v_st_3094_, 2);
lean_inc_ref(v_trees_3096_);
lean_dec_ref(v_st_3094_);
lean_inc(v_toBind_3090_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3097_, 0, v_assignment_3095_);
lean_closure_set(v___f_3097_, 1, v_toPure_3089_);
lean_closure_set(v___f_3097_, 2, v_toBind_3090_);
lean_closure_set(v___f_3097_, 3, v_ctx_x3f_3091_);
v___x_3098_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3092_, v___f_3097_, v_trees_3096_);
v___x_3099_ = lean_apply_4(v_toBind_3090_, lean_box(0), lean_box(0), v___x_3098_, v___f_3093_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3100_, lean_object* v_modifyInfoState_3101_, lean_object* v_toPure_3102_, lean_object* v_toBind_3103_, lean_object* v_ctx_x3f_3104_, lean_object* v_inst_3105_, lean_object* v_getInfoState_3106_, lean_object* v_inst_3107_, lean_object* v_x_3108_, lean_object* v___f_3109_, lean_object* v_treesSaved_3110_){
_start:
{
lean_object* v_map_3111_; lean_object* v___f_3112_; lean_object* v___f_3113_; lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_map_3111_ = lean_ctor_get(v_toFunctor_3100_, 0);
lean_inc(v_map_3111_);
lean_dec_ref(v_toFunctor_3100_);
v___f_3112_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3112_, 0, v_treesSaved_3110_);
lean_closure_set(v___f_3112_, 1, v_modifyInfoState_3101_);
lean_inc(v_toBind_3103_);
v___f_3113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3113_, 0, v_toPure_3102_);
lean_closure_set(v___f_3113_, 1, v_toBind_3103_);
lean_closure_set(v___f_3113_, 2, v_ctx_x3f_3104_);
lean_closure_set(v___f_3113_, 3, v_inst_3105_);
lean_closure_set(v___f_3113_, 4, v___f_3112_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3114_, 0, v_toBind_3103_);
lean_closure_set(v___f_3114_, 1, v_getInfoState_3106_);
lean_closure_set(v___f_3114_, 2, v___f_3113_);
v___x_3115_ = lean_apply_4(v_inst_3107_, lean_box(0), lean_box(0), v_x_3108_, v___f_3114_);
v___x_3116_ = lean_apply_4(v_map_3111_, lean_box(0), lean_box(0), v___f_3109_, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_x_3120_, lean_object* v_ctx_x3f_3121_){
_start:
{
lean_object* v_toApplicative_3122_; lean_object* v_toBind_3123_; lean_object* v_getInfoState_3124_; lean_object* v_modifyInfoState_3125_; lean_object* v_toFunctor_3126_; lean_object* v_toPure_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; 
v_toApplicative_3122_ = lean_ctor_get(v_inst_3117_, 0);
v_toBind_3123_ = lean_ctor_get(v_inst_3117_, 1);
lean_inc_n(v_toBind_3123_, 3);
v_getInfoState_3124_ = lean_ctor_get(v_inst_3118_, 0);
lean_inc_n(v_getInfoState_3124_, 2);
v_modifyInfoState_3125_ = lean_ctor_get(v_inst_3118_, 1);
v_toFunctor_3126_ = lean_ctor_get(v_toApplicative_3122_, 0);
v_toPure_3127_ = lean_ctor_get(v_toApplicative_3122_, 1);
v___f_3128_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3120_);
lean_inc_ref(v_inst_3117_);
lean_inc(v_toPure_3127_);
lean_inc(v_modifyInfoState_3125_);
lean_inc_ref(v_toFunctor_3126_);
v___f_3129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3129_, 0, v_toFunctor_3126_);
lean_closure_set(v___f_3129_, 1, v_modifyInfoState_3125_);
lean_closure_set(v___f_3129_, 2, v_toPure_3127_);
lean_closure_set(v___f_3129_, 3, v_toBind_3123_);
lean_closure_set(v___f_3129_, 4, v_ctx_x3f_3121_);
lean_closure_set(v___f_3129_, 5, v_inst_3117_);
lean_closure_set(v___f_3129_, 6, v_getInfoState_3124_);
lean_closure_set(v___f_3129_, 7, v_inst_3119_);
lean_closure_set(v___f_3129_, 8, v_x_3120_);
lean_closure_set(v___f_3129_, 9, v___f_3128_);
v___f_3130_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3130_, 0, v_x_3120_);
lean_closure_set(v___f_3130_, 1, v_inst_3117_);
lean_closure_set(v___f_3130_, 2, v_inst_3118_);
lean_closure_set(v___f_3130_, 3, v_toBind_3123_);
lean_closure_set(v___f_3130_, 4, v___f_3129_);
v___x_3131_ = lean_apply_4(v_toBind_3123_, lean_box(0), lean_box(0), v_getInfoState_3124_, v___f_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_00_u03b1_3135_, lean_object* v_inst_3136_, lean_object* v_x_3137_, lean_object* v_ctx_x3f_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3133_, v_inst_3134_, v_inst_3136_, v_x_3137_, v_ctx_x3f_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3140_, lean_object* v_____do__lift_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_____do__lift_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v___x_3144_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v_toApplicative_3155_; lean_object* v_toBind_3156_; lean_object* v_toPure_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_toApplicative_3155_ = lean_ctor_get(v_inst_3145_, 0);
v_toBind_3156_ = lean_ctor_get(v_inst_3145_, 1);
v_toPure_3157_ = lean_ctor_get(v_toApplicative_3155_, 1);
lean_inc_ref(v_inst_3145_);
v___x_3158_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3145_, v_inst_3149_, v_inst_3151_, v_inst_3150_, v_inst_3152_, v_inst_3147_, v_inst_3153_);
lean_inc(v_toPure_3157_);
v___f_3159_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3159_, 0, v_toPure_3157_);
lean_inc(v_toBind_3156_);
v___x_3160_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v___x_3158_, v___f_3159_);
v___x_3161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3145_, v_inst_3146_, v_inst_3148_, v_x_3154_, v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_00_u03b1_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_x_3173_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3163_, v_inst_3164_, v_inst_3166_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_inst_3171_, v_inst_3172_, v_x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3175_, lean_object* v_____x_3176_){
_start:
{
if (lean_obj_tag(v_____x_3176_) == 1)
{
lean_object* v_val_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3186_; 
v_val_3177_ = lean_ctor_get(v_____x_3176_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_____x_3176_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3179_ = v_____x_3176_;
v_isShared_3180_ = v_isSharedCheck_3186_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_val_3177_);
lean_dec(v_____x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3186_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_val_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v___x_3181_);
v___x_3183_ = v___x_3179_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_apply_2(v_toPure_3175_, lean_box(0), v___x_3183_);
return v___x_3184_;
}
}
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec(v_____x_3176_);
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_apply_2(v_toPure_3175_, lean_box(0), v___x_3187_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_x_3193_){
_start:
{
lean_object* v_toApplicative_3194_; lean_object* v_toBind_3195_; lean_object* v_toPure_3196_; lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_toApplicative_3194_ = lean_ctor_get(v_inst_3189_, 0);
v_toBind_3195_ = lean_ctor_get(v_inst_3189_, 1);
v_toPure_3196_ = lean_ctor_get(v_toApplicative_3194_, 1);
lean_inc(v_toPure_3196_);
v___f_3197_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3197_, 0, v_toPure_3196_);
lean_inc(v_toBind_3195_);
v___x_3198_ = lean_apply_4(v_toBind_3195_, lean_box(0), lean_box(0), v_inst_3192_, v___f_3197_);
v___x_3199_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3189_, v_inst_3190_, v_inst_3191_, v_x_3193_, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_00_u03b1_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3201_, v_inst_3202_, v_inst_3204_, v_inst_3205_, v_x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3208_, lean_object* v_autoImplicits_3209_){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_autoImplicits_3209_);
v___x_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
v___x_3212_ = lean_apply_2(v_toPure_3208_, lean_box(0), v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v_toApplicative_3218_; lean_object* v_toBind_3219_; lean_object* v_toPure_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_toApplicative_3218_ = lean_ctor_get(v_inst_3213_, 0);
v_toBind_3219_ = lean_ctor_get(v_inst_3213_, 1);
v_toPure_3220_ = lean_ctor_get(v_toApplicative_3218_, 1);
lean_inc(v_toPure_3220_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3221_, 0, v_toPure_3220_);
lean_inc(v_toBind_3219_);
v___x_3222_ = lean_apply_4(v_toBind_3219_, lean_box(0), lean_box(0), v_inst_3216_, v___f_3221_);
v___x_3223_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3213_, v_inst_3214_, v_inst_3215_, v_x_3217_, v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_00_u03b1_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3225_, v_inst_3226_, v_inst_3228_, v_inst_3229_, v_x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3232_, lean_object* v___x_3233_, lean_object* v_mvarId_3234_, lean_object* v_toPure_3235_, lean_object* v_____do__lift_3236_){
_start:
{
lean_object* v_assignment_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_assignment_3237_ = lean_ctor_get(v_____do__lift_3236_, 0);
v___x_3238_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3232_, v___x_3233_, v_assignment_3237_, v_mvarId_3234_);
v___x_3239_ = lean_apply_2(v_toPure_3235_, lean_box(0), v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3240_, lean_object* v___x_3241_, lean_object* v_mvarId_3242_, lean_object* v_toPure_3243_, lean_object* v_____do__lift_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3240_, v___x_3241_, v_mvarId_3242_, v_toPure_3243_, v_____do__lift_3244_);
lean_dec_ref(v_____do__lift_3244_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_mvarId_3250_){
_start:
{
lean_object* v_toApplicative_3251_; lean_object* v_toBind_3252_; lean_object* v_getInfoState_3253_; lean_object* v_toPure_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; 
v_toApplicative_3251_ = lean_ctor_get(v_inst_3248_, 0);
lean_inc_ref(v_toApplicative_3251_);
v_toBind_3252_ = lean_ctor_get(v_inst_3248_, 1);
lean_inc(v_toBind_3252_);
lean_dec_ref(v_inst_3248_);
v_getInfoState_3253_ = lean_ctor_get(v_inst_3249_, 0);
lean_inc(v_getInfoState_3253_);
lean_dec_ref(v_inst_3249_);
v_toPure_3254_ = lean_ctor_get(v_toApplicative_3251_, 1);
lean_inc(v_toPure_3254_);
lean_dec_ref(v_toApplicative_3251_);
v___x_3255_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3256_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3257_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3257_, 0, v___x_3255_);
lean_closure_set(v___f_3257_, 1, v___x_3256_);
lean_closure_set(v___f_3257_, 2, v_mvarId_3250_);
lean_closure_set(v___f_3257_, 3, v_toPure_3254_);
v___x_3258_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v_getInfoState_3253_, v___f_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_mvarId_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3260_, v_inst_3261_, v_mvarId_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_mvarId_3266_, lean_object* v_infoTree_3267_, lean_object* v_s_3268_){
_start:
{
uint8_t v_enabled_3269_; lean_object* v_assignment_3270_; lean_object* v_lazyAssignment_3271_; lean_object* v_trees_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_enabled_3269_ = lean_ctor_get_uint8(v_s_3268_, sizeof(void*)*3);
v_assignment_3270_ = lean_ctor_get(v_s_3268_, 0);
v_lazyAssignment_3271_ = lean_ctor_get(v_s_3268_, 1);
v_trees_3272_ = lean_ctor_get(v_s_3268_, 2);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_s_3268_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v_s_3268_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_trees_3272_);
lean_inc(v_lazyAssignment_3271_);
lean_inc(v_assignment_3270_);
lean_dec(v_s_3268_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3264_, v___x_3265_, v_assignment_3270_, v_mvarId_3266_, v_infoTree_3267_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_lazyAssignment_3271_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_trees_3272_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*3, v_enabled_3269_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3285_ = lean_unsigned_to_nat(2u);
v___x_3286_ = lean_unsigned_to_nat(384u);
v___x_3287_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3288_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3289_ = l_mkPanicMessageWithDecl(v___x_3288_, v___x_3287_, v___x_3286_, v___x_3285_, v___x_3284_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3290_, lean_object* v___f_3291_, lean_object* v___x_3292_, lean_object* v_____do__lift_3293_){
_start:
{
if (lean_obj_tag(v_____do__lift_3293_) == 0)
{
lean_object* v_modifyInfoState_3294_; lean_object* v___x_3295_; 
v_modifyInfoState_3294_ = lean_ctor_get(v_inst_3290_, 1);
lean_inc(v_modifyInfoState_3294_);
lean_dec_ref(v_inst_3290_);
v___x_3295_ = lean_apply_1(v_modifyInfoState_3294_, v___f_3291_);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec_ref(v___f_3291_);
lean_dec_ref(v_inst_3290_);
v___x_3296_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3297_ = l_panic___redArg(v___x_3292_, v___x_3296_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3298_, lean_object* v___f_3299_, lean_object* v___x_3300_, lean_object* v_____do__lift_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3298_, v___f_3299_, v___x_3300_, v_____do__lift_3301_);
lean_dec(v_____do__lift_3301_);
lean_dec(v___x_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_mvarId_3305_, lean_object* v_infoTree_3306_){
_start:
{
lean_object* v_toBind_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___f_3314_; lean_object* v___x_3315_; 
v_toBind_3307_ = lean_ctor_get(v_inst_3303_, 1);
lean_inc(v_toBind_3307_);
v___x_3308_ = lean_box(0);
v___x_3309_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3310_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3305_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3311_, 0, v___x_3309_);
lean_closure_set(v___f_3311_, 1, v___x_3310_);
lean_closure_set(v___f_3311_, 2, v_mvarId_3305_);
lean_closure_set(v___f_3311_, 3, v_infoTree_3306_);
lean_inc_ref(v_inst_3304_);
lean_inc_ref(v_inst_3303_);
v___x_3312_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3303_, v_inst_3304_, v_mvarId_3305_);
v___x_3313_ = l_instInhabitedOfMonad___redArg(v_inst_3303_, v___x_3308_);
v___f_3314_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3314_, 0, v_inst_3304_);
lean_closure_set(v___f_3314_, 1, v___f_3311_);
lean_closure_set(v___f_3314_, 2, v___x_3313_);
v___x_3315_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v___x_3312_, v___f_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_mvarId_3319_, lean_object* v_infoTree_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3317_, v_inst_3318_, v_mvarId_3319_, v_infoTree_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3322_, lean_object* v_output_3323_, lean_object* v_toPure_3324_, lean_object* v_____do__lift_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3326_, 0, v_____do__lift_3325_);
lean_ctor_set(v___x_3326_, 1, v_stx_3322_);
lean_ctor_set(v___x_3326_, 2, v_output_3323_);
v___x_3327_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
v___x_3328_ = lean_apply_2(v_toPure_3324_, lean_box(0), v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_stx_3333_, lean_object* v_output_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v_toApplicative_3336_; lean_object* v_toBind_3337_; lean_object* v_toPure_3338_; lean_object* v___f_3339_; lean_object* v_mkInfo_3340_; lean_object* v___f_3341_; lean_object* v___x_3342_; 
v_toApplicative_3336_ = lean_ctor_get(v_inst_3330_, 0);
v_toBind_3337_ = lean_ctor_get(v_inst_3330_, 1);
v_toPure_3338_ = lean_ctor_get(v_toApplicative_3336_, 1);
lean_inc_n(v_toPure_3338_, 2);
v___f_3339_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3339_, 0, v_stx_3333_);
lean_closure_set(v___f_3339_, 1, v_output_3334_);
lean_closure_set(v___f_3339_, 2, v_toPure_3338_);
lean_inc_n(v_toBind_3337_, 2);
v_mkInfo_3340_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v_inst_3332_, v___f_3339_);
v___f_3341_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3341_, 0, v_toPure_3338_);
lean_closure_set(v___f_3341_, 1, v_toBind_3337_);
lean_closure_set(v___f_3341_, 2, v_mkInfo_3340_);
v___x_3342_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3330_, v_inst_3331_, v_inst_3329_, v_x_3335_, v___f_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3343_, lean_object* v_00_u03b1_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_stx_3349_, lean_object* v_output_3350_, lean_object* v_x_3351_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3345_, v_inst_3346_, v_inst_3347_, v_inst_3348_, v_stx_3349_, v_output_3350_, v_x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3353_, lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v___x_3356_, lean_object* v_mvarId_3357_, lean_object* v_s_3358_){
_start:
{
lean_object* v_trees_3359_; uint8_t v_enabled_3360_; lean_object* v_assignment_3361_; lean_object* v_lazyAssignment_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3379_; 
v_trees_3359_ = lean_ctor_get(v_s_3358_, 2);
v_enabled_3360_ = lean_ctor_get_uint8(v_s_3358_, sizeof(void*)*3);
v_assignment_3361_ = lean_ctor_get(v_s_3358_, 0);
v_lazyAssignment_3362_ = lean_ctor_get(v_s_3358_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_s_3358_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3364_ = v_s_3358_;
v_isShared_3365_ = v_isSharedCheck_3379_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_trees_3359_);
lean_inc(v_lazyAssignment_3362_);
lean_inc(v_assignment_3361_);
lean_dec(v_s_3358_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3379_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_size_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v_size_3366_ = lean_ctor_get(v_trees_3359_, 2);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_nat_dec_lt(v___x_3367_, v_size_3366_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3370_; 
lean_dec_ref(v_trees_3359_);
lean_dec(v_mvarId_3357_);
lean_dec_ref(v___x_3356_);
lean_dec_ref(v___x_3355_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 2, v_treesSaved_3353_);
v___x_3370_ = v___x_3364_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_assignment_3361_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_lazyAssignment_3362_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_treesSaved_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3371_, sizeof(void*)*3, v_enabled_3360_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_sub(v_size_3366_, v___x_3372_);
v___x_3374_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3354_, v_trees_3359_, v___x_3373_);
lean_dec(v___x_3373_);
lean_dec_ref(v_trees_3359_);
v___x_3375_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3355_, v___x_3356_, v_assignment_3361_, v_mvarId_3357_, v___x_3374_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 2, v_treesSaved_3353_);
lean_ctor_set(v___x_3364_, 0, v___x_3375_);
v___x_3377_ = v___x_3364_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_lazyAssignment_3362_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_treesSaved_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3378_, sizeof(void*)*3, v_enabled_3360_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3380_, lean_object* v___x_3381_, lean_object* v___x_3382_, lean_object* v___x_3383_, lean_object* v_mvarId_3384_, lean_object* v_s_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3380_, v___x_3381_, v___x_3382_, v___x_3383_, v_mvarId_3384_, v_s_3385_);
lean_dec_ref(v___x_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3387_, lean_object* v___f_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_apply_1(v_modifyInfoState_3387_, v___f_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3391_, lean_object* v___f_3392_, lean_object* v_x_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3391_, v___f_3392_, v_x_3393_);
lean_dec(v_x_3393_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3395_, lean_object* v___x_3396_, lean_object* v___x_3397_, lean_object* v___x_3398_, lean_object* v_mvarId_3399_, lean_object* v_modifyInfoState_3400_, lean_object* v_inst_3401_, lean_object* v_x_3402_, lean_object* v___f_3403_, lean_object* v_treesSaved_3404_){
_start:
{
lean_object* v_map_3405_; lean_object* v___f_3406_; lean_object* v___f_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_map_3405_ = lean_ctor_get(v_toFunctor_3395_, 0);
lean_inc(v_map_3405_);
lean_dec_ref(v_toFunctor_3395_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3406_, 0, v_treesSaved_3404_);
lean_closure_set(v___f_3406_, 1, v___x_3396_);
lean_closure_set(v___f_3406_, 2, v___x_3397_);
lean_closure_set(v___f_3406_, 3, v___x_3398_);
lean_closure_set(v___f_3406_, 4, v_mvarId_3399_);
v___f_3407_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3407_, 0, v_modifyInfoState_3400_);
lean_closure_set(v___f_3407_, 1, v___f_3406_);
v___x_3408_ = lean_apply_4(v_inst_3401_, lean_box(0), lean_box(0), v_x_3402_, v___f_3407_);
v___x_3409_ = lean_apply_4(v_map_3405_, lean_box(0), lean_box(0), v___f_3403_, v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3410_, lean_object* v_inst_3411_, lean_object* v_inst_3412_, lean_object* v_mvarId_3413_, lean_object* v_x_3414_){
_start:
{
lean_object* v_toApplicative_3415_; lean_object* v_toBind_3416_; lean_object* v_getInfoState_3417_; lean_object* v_modifyInfoState_3418_; lean_object* v_toFunctor_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___f_3424_; lean_object* v___f_3425_; lean_object* v___x_3426_; 
v_toApplicative_3415_ = lean_ctor_get(v_inst_3411_, 0);
v_toBind_3416_ = lean_ctor_get(v_inst_3411_, 1);
lean_inc_n(v_toBind_3416_, 2);
v_getInfoState_3417_ = lean_ctor_get(v_inst_3412_, 0);
lean_inc(v_getInfoState_3417_);
v_modifyInfoState_3418_ = lean_ctor_get(v_inst_3412_, 1);
v_toFunctor_3419_ = lean_ctor_get(v_toApplicative_3415_, 0);
v___f_3420_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3421_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3422_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3423_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3414_);
lean_inc(v_modifyInfoState_3418_);
lean_inc_ref(v_toFunctor_3419_);
v___f_3424_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3424_, 0, v_toFunctor_3419_);
lean_closure_set(v___f_3424_, 1, v___x_3423_);
lean_closure_set(v___f_3424_, 2, v___x_3421_);
lean_closure_set(v___f_3424_, 3, v___x_3422_);
lean_closure_set(v___f_3424_, 4, v_mvarId_3413_);
lean_closure_set(v___f_3424_, 5, v_modifyInfoState_3418_);
lean_closure_set(v___f_3424_, 6, v_inst_3410_);
lean_closure_set(v___f_3424_, 7, v_x_3414_);
lean_closure_set(v___f_3424_, 8, v___f_3420_);
v___f_3425_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3425_, 0, v_x_3414_);
lean_closure_set(v___f_3425_, 1, v_inst_3411_);
lean_closure_set(v___f_3425_, 2, v_inst_3412_);
lean_closure_set(v___f_3425_, 3, v_toBind_3416_);
lean_closure_set(v___f_3425_, 4, v___f_3424_);
v___x_3426_ = lean_apply_4(v_toBind_3416_, lean_box(0), lean_box(0), v_getInfoState_3417_, v___f_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3427_, lean_object* v_00_u03b1_3428_, lean_object* v_inst_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_mvarId_3432_, lean_object* v_x_3433_){
_start:
{
lean_object* v_toApplicative_3434_; lean_object* v_toBind_3435_; lean_object* v_getInfoState_3436_; lean_object* v_modifyInfoState_3437_; lean_object* v_toFunctor_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___f_3443_; lean_object* v___f_3444_; lean_object* v___x_3445_; 
v_toApplicative_3434_ = lean_ctor_get(v_inst_3430_, 0);
v_toBind_3435_ = lean_ctor_get(v_inst_3430_, 1);
lean_inc_n(v_toBind_3435_, 2);
v_getInfoState_3436_ = lean_ctor_get(v_inst_3431_, 0);
lean_inc(v_getInfoState_3436_);
v_modifyInfoState_3437_ = lean_ctor_get(v_inst_3431_, 1);
v_toFunctor_3438_ = lean_ctor_get(v_toApplicative_3434_, 0);
v___f_3439_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3440_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3441_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3442_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3433_);
lean_inc(v_modifyInfoState_3437_);
lean_inc_ref(v_toFunctor_3438_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3443_, 0, v_toFunctor_3438_);
lean_closure_set(v___f_3443_, 1, v___x_3442_);
lean_closure_set(v___f_3443_, 2, v___x_3440_);
lean_closure_set(v___f_3443_, 3, v___x_3441_);
lean_closure_set(v___f_3443_, 4, v_mvarId_3432_);
lean_closure_set(v___f_3443_, 5, v_modifyInfoState_3437_);
lean_closure_set(v___f_3443_, 6, v_inst_3429_);
lean_closure_set(v___f_3443_, 7, v_x_3433_);
lean_closure_set(v___f_3443_, 8, v___f_3439_);
v___f_3444_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3444_, 0, v_x_3433_);
lean_closure_set(v___f_3444_, 1, v_inst_3430_);
lean_closure_set(v___f_3444_, 2, v_inst_3431_);
lean_closure_set(v___f_3444_, 3, v_toBind_3435_);
lean_closure_set(v___f_3444_, 4, v___f_3443_);
v___x_3445_ = lean_apply_4(v_toBind_3435_, lean_box(0), lean_box(0), v_getInfoState_3436_, v___f_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3446_, lean_object* v_s_3447_){
_start:
{
lean_object* v_assignment_3448_; lean_object* v_lazyAssignment_3449_; lean_object* v_trees_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_assignment_3448_ = lean_ctor_get(v_s_3447_, 0);
v_lazyAssignment_3449_ = lean_ctor_get(v_s_3447_, 1);
v_trees_3450_ = lean_ctor_get(v_s_3447_, 2);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_s_3447_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v_s_3447_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_trees_3450_);
lean_inc(v_lazyAssignment_3449_);
lean_inc(v_assignment_3448_);
lean_dec(v_s_3447_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_assignment_3448_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_lazyAssignment_3449_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_trees_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*3, v_flag_3446_);
return v___x_3455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3458_, lean_object* v_s_3459_){
_start:
{
uint8_t v_flag_boxed_3460_; lean_object* v_res_3461_; 
v_flag_boxed_3460_ = lean_unbox(v_flag_3458_);
v_res_3461_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3460_, v_s_3459_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3462_, uint8_t v_flag_3463_){
_start:
{
lean_object* v_modifyInfoState_3464_; lean_object* v___x_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; 
v_modifyInfoState_3464_ = lean_ctor_get(v_inst_3462_, 1);
lean_inc(v_modifyInfoState_3464_);
lean_dec_ref(v_inst_3462_);
v___x_3465_ = lean_box(v_flag_3463_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3466_, 0, v___x_3465_);
v___x_3467_ = lean_apply_1(v_modifyInfoState_3464_, v___f_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3468_, lean_object* v_flag_3469_){
_start:
{
uint8_t v_flag_boxed_3470_; lean_object* v_res_3471_; 
v_flag_boxed_3470_ = lean_unbox(v_flag_3469_);
v_res_3471_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3468_, v_flag_boxed_3470_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3472_, lean_object* v_inst_3473_, uint8_t v_flag_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3473_, v_flag_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3476_, lean_object* v_inst_3477_, lean_object* v_flag_3478_){
_start:
{
uint8_t v_flag_boxed_3479_; lean_object* v_res_3480_; 
v_flag_boxed_3479_ = lean_unbox(v_flag_3478_);
v_res_3480_ = l_Lean_Elab_enableInfoTree(v_m_3476_, v_inst_3477_, v_flag_boxed_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3481_){
_start:
{
lean_object* v_fst_3482_; 
v_fst_3482_ = lean_ctor_get(v_x_3481_, 0);
lean_inc(v_fst_3482_);
return v_fst_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3483_);
lean_dec_ref(v_x_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3485_, lean_object* v_____r_3486_){
_start:
{
lean_inc(v_x_3485_);
return v_x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3487_, lean_object* v_____r_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3487_, v_____r_3488_);
lean_dec(v_x_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3490_, lean_object* v_x_3491_){
_start:
{
lean_inc(v___x_3490_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3492_, lean_object* v_x_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3492_, v_x_3493_);
lean_dec(v_x_3493_);
lean_dec(v___x_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3495_, lean_object* v_inst_3496_, uint8_t v_flag_3497_, lean_object* v_toBind_3498_, lean_object* v___f_3499_, lean_object* v_inst_3500_, lean_object* v___f_3501_, lean_object* v_____do__lift_3502_){
_start:
{
uint8_t v_enabled_3503_; lean_object* v_map_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v_y_3509_; lean_object* v___x_3510_; 
v_enabled_3503_ = lean_ctor_get_uint8(v_____do__lift_3502_, sizeof(void*)*3);
v_map_3504_ = lean_ctor_get(v_toFunctor_3495_, 0);
lean_inc(v_map_3504_);
lean_dec_ref(v_toFunctor_3495_);
lean_inc_ref(v_inst_3496_);
v___x_3505_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3496_, v_flag_3497_);
v___x_3506_ = lean_apply_4(v_toBind_3498_, lean_box(0), lean_box(0), v___x_3505_, v___f_3499_);
v___x_3507_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3496_, v_enabled_3503_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3508_, 0, v___x_3507_);
v_y_3509_ = lean_apply_4(v_inst_3500_, lean_box(0), lean_box(0), v___x_3506_, v___f_3508_);
v___x_3510_ = lean_apply_4(v_map_3504_, lean_box(0), lean_box(0), v___f_3501_, v_y_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3511_, lean_object* v_inst_3512_, lean_object* v_flag_3513_, lean_object* v_toBind_3514_, lean_object* v___f_3515_, lean_object* v_inst_3516_, lean_object* v___f_3517_, lean_object* v_____do__lift_3518_){
_start:
{
uint8_t v_flag_boxed_3519_; lean_object* v_res_3520_; 
v_flag_boxed_3519_ = lean_unbox(v_flag_3513_);
v_res_3520_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3511_, v_inst_3512_, v_flag_boxed_3519_, v_toBind_3514_, v___f_3515_, v_inst_3516_, v___f_3517_, v_____do__lift_3518_);
lean_dec_ref(v_____do__lift_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, uint8_t v_flag_3525_, lean_object* v_x_3526_){
_start:
{
lean_object* v_toApplicative_3527_; lean_object* v_toBind_3528_; lean_object* v_getInfoState_3529_; lean_object* v_toFunctor_3530_; lean_object* v___f_3531_; lean_object* v___f_3532_; lean_object* v___x_3533_; lean_object* v___f_3534_; lean_object* v___x_3535_; 
v_toApplicative_3527_ = lean_ctor_get(v_inst_3522_, 0);
lean_inc_ref(v_toApplicative_3527_);
v_toBind_3528_ = lean_ctor_get(v_inst_3522_, 1);
lean_inc_n(v_toBind_3528_, 2);
lean_dec_ref(v_inst_3522_);
v_getInfoState_3529_ = lean_ctor_get(v_inst_3523_, 0);
lean_inc(v_getInfoState_3529_);
v_toFunctor_3530_ = lean_ctor_get(v_toApplicative_3527_, 0);
lean_inc_ref(v_toFunctor_3530_);
lean_dec_ref(v_toApplicative_3527_);
v___f_3531_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3532_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3532_, 0, v_x_3526_);
v___x_3533_ = lean_box(v_flag_3525_);
v___f_3534_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3534_, 0, v_toFunctor_3530_);
lean_closure_set(v___f_3534_, 1, v_inst_3523_);
lean_closure_set(v___f_3534_, 2, v___x_3533_);
lean_closure_set(v___f_3534_, 3, v_toBind_3528_);
lean_closure_set(v___f_3534_, 4, v___f_3532_);
lean_closure_set(v___f_3534_, 5, v_inst_3524_);
lean_closure_set(v___f_3534_, 6, v___f_3531_);
v___x_3535_ = lean_apply_4(v_toBind_3528_, lean_box(0), lean_box(0), v_getInfoState_3529_, v___f_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_flag_3539_, lean_object* v_x_3540_){
_start:
{
uint8_t v_flag_boxed_3541_; lean_object* v_res_3542_; 
v_flag_boxed_3541_ = lean_unbox(v_flag_3539_);
v_res_3542_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3536_, v_inst_3537_, v_inst_3538_, v_flag_boxed_3541_, v_x_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3543_, lean_object* v_00_u03b1_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, uint8_t v_flag_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3545_, v_inst_3546_, v_inst_3547_, v_flag_3548_, v_x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3551_, lean_object* v_00_u03b1_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_flag_3556_, lean_object* v_x_3557_){
_start:
{
uint8_t v_flag_boxed_3558_; lean_object* v_res_3559_; 
v_flag_boxed_3558_ = lean_unbox(v_flag_3556_);
v_res_3559_ = l_Lean_Elab_withEnableInfoTree(v_m_3551_, v_00_u03b1_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_flag_boxed_3558_, v_x_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3560_, lean_object* v_____do__lift_3561_){
_start:
{
lean_object* v_trees_3562_; lean_object* v___x_3563_; 
v_trees_3562_ = lean_ctor_get(v_____do__lift_3561_, 2);
lean_inc_ref(v_trees_3562_);
lean_dec_ref(v_____do__lift_3561_);
v___x_3563_ = lean_apply_2(v_toPure_3560_, lean_box(0), v_trees_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3564_, lean_object* v_inst_3565_){
_start:
{
lean_object* v_toApplicative_3566_; lean_object* v_toBind_3567_; lean_object* v_getInfoState_3568_; lean_object* v_toPure_3569_; lean_object* v___f_3570_; lean_object* v___x_3571_; 
v_toApplicative_3566_ = lean_ctor_get(v_inst_3565_, 0);
lean_inc_ref(v_toApplicative_3566_);
v_toBind_3567_ = lean_ctor_get(v_inst_3565_, 1);
lean_inc(v_toBind_3567_);
lean_dec_ref(v_inst_3565_);
v_getInfoState_3568_ = lean_ctor_get(v_inst_3564_, 0);
lean_inc(v_getInfoState_3568_);
lean_dec_ref(v_inst_3564_);
v_toPure_3569_ = lean_ctor_get(v_toApplicative_3566_, 1);
lean_inc(v_toPure_3569_);
lean_dec_ref(v_toApplicative_3566_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3570_, 0, v_toPure_3569_);
v___x_3571_ = lean_apply_4(v_toBind_3567_, lean_box(0), lean_box(0), v_getInfoState_3568_, v___f_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3573_, v_inst_3574_);
return v___x_3575_;
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
